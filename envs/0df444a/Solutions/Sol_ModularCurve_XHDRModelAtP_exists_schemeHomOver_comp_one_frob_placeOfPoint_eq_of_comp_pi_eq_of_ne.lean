-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_one_frob_placeOfPoint_eq_of_comp_pi_eq_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/4c163f1d-e463-5c29-951e-c6ebc1a17fec

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Theorems.Thm_AlgebraicGeometry_mem_smoothLocus_of_not_mem_range_of_isClosedImmersion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_one_frob_placeOfPoint_eq_of_comp_pi_eq_of_ne
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel

open scoped MatrixGroups TensorProduct

namespace PiFibre

theorem unramified_sections_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    {O : Type u} [CommRing O] [IsLocalRing O]
    (a b : Spec (CommRingCat.of O) ⟶ X) (hf : a ≫ f = b ≫ f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of O))
    (ht : IsLocalRing.closedPoint O ∈ Set.range t.base)
    (hab : t ≫ a = t ≫ b) : a = b := by

  set c : Spec (CommRingCat.of O) ⟶ pullback f f := pullback.lift a b hf with hc
  set E := pullback c (pullback.diagonal f)
  have hE : IsOpenImmersion (pullback.fst c (pullback.diagonal f)) := inferInstance

  have htc : t ≫ c = (t ≫ a) ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · rw [Category.assoc, hc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, hc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id, hab]
  have hrange : Set.range (pullback.fst c (pullback.diagonal f)).base = Set.univ := by
    obtain ⟨t₀, ht₀⟩ := ht
    have hmem : IsLocalRing.closedPoint O ∈ Set.range (pullback.fst c (pullback.diagonal f)).base := by
      refine ⟨(pullback.lift t (t ≫ a) htc).base t₀, ?_⟩
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst, ht₀]
    apply Set.eq_univ_of_forall
    intro x
    exact (IsLocalRing.specializes_closedPoint x).mem_open
      (pullback.fst c (pullback.diagonal f)).isOpenEmbedding.isOpen_range hmem
  have hepi : Epi (pullback.fst c (pullback.diagonal f)).base := by
    rw [TopCat.epi_iff_surjective]
    exact Set.range_eq_univ.mp hrange
  have hiso : IsIso (pullback.fst c (pullback.diagonal f)) := IsOpenImmersion.isIso _

  have hfac : c = (inv (pullback.fst c (pullback.diagonal f)) ≫ pullback.snd c (pullback.diagonal f)) ≫
      pullback.diagonal f := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  have ha : a = inv (pullback.fst c (pullback.diagonal f)) ≫ pullback.snd c (pullback.diagonal f) := by
    have := congrArg (· ≫ pullback.fst f f) hfac
    simp only [hc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id] at this
    exact this
  have hb : b = inv (pullback.fst c (pullback.diagonal f)) ≫ pullback.snd c (pullback.diagonal f) := by
    have := congrArg (· ≫ pullback.snd f f) hfac
    simp only [hc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id] at this
    exact this
  rw [ha, hb]

end PiFibre

namespace PiFibre

theorem valuative_section
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f] [IsSeparated f]
    (x : Spec (CommRingCat.of K) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃! σ : Spec (CommRingCat.of R) ⟶ X,
      σ ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ = x := by
  let S : ValuativeCommSq f := ValuativeCommSq.mk R K x (𝟙 _) ⟨by rw [Category.comp_id]; exact hx⟩
  have hE : S.commSq.HasLift := by
    have h := UniversallyClosed.eq_valuativeCriterion
    have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) f := h ▸ (inferInstance : UniversallyClosed f)
    exact this.1 S
  have hU : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion f S
  refine ⟨S.commSq.lift, ⟨S.commSq.fac_right, S.commSq.fac_left⟩, ?_⟩
  rintro σ ⟨h1, h2⟩
  let l₁ : S.commSq.LiftStruct := ⟨σ, h2, h1⟩
  let l₂ : S.commSq.LiftStruct := ⟨S.commSq.lift, S.commSq.fac_left, S.commSq.fac_right⟩
  exact congrArg CommSq.LiftStruct.l (Subsingleton.elim l₁ l₂)

theorem smooth_smoothLocus_ι_comp {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    Smooth (f.smoothLocus.ι ≫ f) := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
  exact Scheme.Opens.ι_preimage_self _

end PiFibre
namespace PiFibre

theorem isUnramifiedAt_of_subsingleton_tensorProduct
    {R S K : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
    [Field K] [Algebra S K] (P : Ideal S) [P.IsPrime]
    (hP : RingHom.ker (algebraMap S K) = P)
    (h : Subsingleton (K ⊗[S] Ω[S⁄R])) : Algebra.IsUnramifiedAt R P := by
  have h1 : P ≤ RingHom.ker (algebraMap S K) := hP.ge
  have h2 : P.primeCompl ≤ (IsUnit.submonoid K).comap (algebraMap S K) := by
    intro s hs
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    intro h0
    exact hs (hP ▸ (RingHom.mem_ker).mpr h0)
  let g : P.ResidueField →+* K := Ideal.ResidueField.lift P (algebraMap S K) h1 h2
  letI : Algebra P.ResidueField K := g.toAlgebra
  haveI : IsScalarTower S P.ResidueField K :=
    IsScalarTower.of_algebraMap_eq fun s => (Ideal.ResidueField.lift_algebraMap P (algebraMap S K) h1 h2 s).symm
  have e := TensorProduct.AlgebraTensorModule.cancelBaseChange S P.ResidueField K K Ω[S⁄R]
  have hK : Subsingleton (K ⊗[P.ResidueField] (P.ResidueField ⊗[S] Ω[S⁄R])) := e.toEquiv.subsingleton
  have hκ : Subsingleton (P.ResidueField ⊗[S] Ω[S⁄R]) :=
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right (R := P.ResidueField) (M := K)).mp hK
  change (⟨P, inferInstance⟩ : PrimeSpectrum S) ∈ Algebra.unramifiedLocus R S
  rw [Algebra.unramifiedLocus_eq_compl_support, Set.mem_compl_iff,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  exact not_nontrivial_iff_subsingleton.mpr hκ

theorem subsingleton_residueField_tensorProduct_of_isUnramifiedAt
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
    (Q : Ideal S) [Q.IsPrime] [Algebra.IsUnramifiedAt R Q] :
    Subsingleton (Q.ResidueField ⊗[S] Ω[S⁄R]) := by
  have hmem : (⟨Q, inferInstance⟩ : PrimeSpectrum S) ∈ Algebra.unramifiedLocus R S := ‹_›
  rw [Algebra.unramifiedLocus_eq_compl_support, Set.mem_compl_iff,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hmem
  exact not_nontrivial_iff_subsingleton.mp hmem

theorem exists_formallyUnramified_away_of_baseChange
    {R₀ B B' κ : Type*} [CommRing R₀] [CommRing B] [CommRing B'] [CommRing κ]
    [Algebra R₀ B] [Algebra R₀ B'] [Algebra R₀ κ] (φ : B' →ₐ[R₀] B) (hφ : φ.toRingHom.FiniteType)
    (q : Ideal (B ⊗[R₀] κ)) [q.IsPrime] (g : B ⊗[R₀] κ) (hg : g ∉ q)
    (hψ : ((algebraMap (B ⊗[R₀] κ) (Localization.Away g)).comp
      (Algebra.TensorProduct.map φ (AlgHom.id R₀ κ)).toRingHom).FormallyUnramified) :
    ∃ f : B, f ∉ q.comap (algebraMap B (B ⊗[R₀] κ)) ∧
      ((algebraMap B (Localization.Away f)).comp φ.toRingHom).FormallyUnramified := by

  letI iB : Algebra B' B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R₀ B' B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  haveI : Algebra.FiniteType B' B := (RingHom.finiteType_algebraMap).mp hφ
  let φκ : B' ⊗[R₀] κ →ₐ[R₀] B ⊗[R₀] κ := Algebra.TensorProduct.map φ (AlgHom.id R₀ κ)
  letI iκ : Algebra (B' ⊗[R₀] κ) (B ⊗[R₀] κ) := φκ.toRingHom.toAlgebra
  haveI : IsScalarTower B' (B' ⊗[R₀] κ) (B ⊗[R₀] κ) := IsScalarTower.of_algebraMap_eq fun b => by
    show algebraMap B (B ⊗[R₀] κ) (φ b) = φκ (b ⊗ₜ 1)
    simp [φκ, Algebra.TensorProduct.algebraMap_apply]

  haveI hpo : Algebra.IsPushout B' B (B' ⊗[R₀] κ) (B ⊗[R₀] κ) :=
    Algebra.IsPushout.tensorProduct_tensorProduct R₀ κ B' B (by ext k; simp [φκ, RingHom.algebraMap_toAlgebra])
  haveI hpo' : Algebra.IsPushout B' (B' ⊗[R₀] κ) B (B ⊗[R₀] κ) := hpo.symm
  haveI : Algebra.FiniteType (B' ⊗[R₀] κ) (B ⊗[R₀] κ) :=
    Algebra.FiniteType.equiv inferInstance (Algebra.IsPushout.equiv B' (B' ⊗[R₀] κ) B (B ⊗[R₀] κ))

  have hFU : Algebra.FormallyUnramified (B' ⊗[R₀] κ) (Localization.Away g) := by
    rw [← RingHom.formallyUnramified_algebraMap,
      IsScalarTower.algebraMap_eq (B' ⊗[R₀] κ) (B ⊗[R₀] κ) (Localization.Away g)]
    exact hψ
  haveI hq : Algebra.IsUnramifiedAt (B' ⊗[R₀] κ) q :=
    Algebra.basicOpen_subset_unramifiedLocus_iff.mpr hFU (show (⟨q, inferInstance⟩ : PrimeSpectrum _) ∈ _ from hg)
  have h1 : Subsingleton (q.ResidueField ⊗[B ⊗[R₀] κ] Ω[(B ⊗[R₀] κ)⁄(B' ⊗[R₀] κ)]) :=
    subsingleton_residueField_tensorProduct_of_isUnramifiedAt q

  have e1 := KaehlerDifferential.tensorKaehlerEquiv B' (B' ⊗[R₀] κ) B (B ⊗[R₀] κ)
  have e2 : q.ResidueField ⊗[B ⊗[R₀] κ] ((B ⊗[R₀] κ) ⊗[B] Ω[B⁄B']) ≃ₗ[q.ResidueField]
      q.ResidueField ⊗[B ⊗[R₀] κ] Ω[(B ⊗[R₀] κ)⁄(B' ⊗[R₀] κ)] :=
    LinearEquiv.baseChange (B ⊗[R₀] κ) q.ResidueField _ _ e1
  have e3 := TensorProduct.AlgebraTensorModule.cancelBaseChange B (B ⊗[R₀] κ) q.ResidueField q.ResidueField Ω[B⁄B']
  have h2 : Subsingleton (q.ResidueField ⊗[B] Ω[B⁄B']) :=
    e3.symm.toEquiv.subsingleton_congr.mpr (e2.toEquiv.subsingleton_congr.mpr h1)

  have hker : RingHom.ker (algebraMap B q.ResidueField) = q.comap (algebraMap B (B ⊗[R₀] κ)) := by
    rw [IsScalarTower.algebraMap_eq B (B ⊗[R₀] κ) q.ResidueField, ← RingHom.comap_ker,
      Ideal.ker_algebraMap_residueField]
  haveI : (q.comap (algebraMap B (B ⊗[R₀] κ))).IsPrime := Ideal.IsPrime.comap _
  haveI : Algebra.IsUnramifiedAt B' (q.comap (algebraMap B (B ⊗[R₀] κ))) :=
    isUnramifiedAt_of_subsingleton_tensorProduct (R := B') _ hker h2
  obtain ⟨f, hf, hfU⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := B') (q.comap (algebraMap B (B ⊗[R₀] κ)))
  refine ⟨f, hf, ?_⟩
  rw [show (algebraMap B (Localization.Away f)).comp φ.toRingHom = algebraMap B' (Localization.Away f) from
    (IsScalarTower.algebraMap_eq B' B (Localization.Away f)).symm, RingHom.formallyUnramified_algebraMap]
  exact hfU

theorem exists_formallyUnramified_away_of_isOpenImmersion_fibre
    {R₀ B B' : Type u} [CommRing R₀] [CommRing B] [CommRing B'] [Algebra R₀ B] [Algebra R₀ B']
    (φ : B' →ₐ[R₀] B) (hφ : φ.toRingHom.FiniteType)
    {XM XN : Scheme.{u}} (tM : XM ⟶ Spec (CommRingCat.of R₀)) (tN : XN ⟶ Spec (CommRingCat.of R₀))
    (π : XM ⟶ XN)
    (ι : Spec (CommRingCat.of B) ⟶ XM) [IsOpenImmersion ι] (ι' : Spec (CommRingCat.of B') ⟶ XN) [IsOpenImmersion ι']
    (hι : ι ≫ tM = Spec.map (CommRingCat.ofHom (algebraMap R₀ B)))
    (hι' : ι' ≫ tN = Spec.map (CommRingCat.ofHom (algebraMap R₀ B')))
    (hchart : ι ≫ π = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ι')
    {κ : Type u} [Field κ] (τ : R₀ →+* κ)
    (πκ : pullback tM (Spec.map (CommRingCat.ofHom τ)) ⟶ pullback tN (Spec.map (CommRingCat.ofHom τ)))
    (hπκ₁ : πκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π) (hπκ₂ : πκ ≫ pullback.snd _ _ = pullback.snd _ _)
    (x : ↥(pullback tM (Spec.map (CommRingCat.ofHom τ))))
    (hx : (pullback.fst tM (Spec.map (CommRingCat.ofHom τ))).base x ∈ Set.range ι.base)
    (V₀ : (pullback tM (Spec.map (CommRingCat.ofHom τ))).Opens) (hxV : x ∈ V₀)
    (hV : IsOpenImmersion (V₀.ι ≫ πκ)) :
    ∃ (W : Scheme.{u}) (w : W ⟶ XM), IsOpenImmersion w ∧
      (pullback.fst tM (Spec.map (CommRingCat.ofHom τ))).base x ∈ Set.range w.base ∧
      FormallyUnramified (w ≫ π) := by
  classical
  letI : Algebra R₀ κ := τ.toAlgebra
  let sκ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R₀) := Spec.map (CommRingCat.ofHom τ)

  have eB₁ : Spec.map (CommRingCat.ofHom (algebraMap R₀ B)) ≫ 𝟙 _ = ι ≫ tM := by rw [Category.comp_id, hι]
  have eB'₁ : Spec.map (CommRingCat.ofHom (algebraMap R₀ B')) ≫ 𝟙 _ = ι' ≫ tN := by rw [Category.comp_id, hι']
  have eB₂ : sκ ≫ 𝟙 _ = 𝟙 _ ≫ sκ := by rw [Category.comp_id, Category.id_comp]
  let jB : Spec (CommRingCat.of (B ⊗[R₀] κ)) ⟶ pullback tM sκ :=
    (pullbackSpecIso R₀ B κ).inv ≫ pullback.map _ _ _ _ ι (𝟙 _) (𝟙 _) eB₁ eB₂
  let jB' : Spec (CommRingCat.of (B' ⊗[R₀] κ)) ⟶ pullback tN sκ :=
    (pullbackSpecIso R₀ B' κ).inv ≫ pullback.map _ _ _ _ ι' (𝟙 _) (𝟙 _) eB'₁ eB₂
  haveI : IsOpenImmersion jB := inferInstance
  haveI : IsOpenImmersion jB' := inferInstance
  have jB_fst : jB ≫ pullback.fst tM sκ =
      Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[R₀] κ))) ≫ ι := by
    simp only [jB, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc, pullbackSpecIso_inv_fst']
  have jB_snd : jB ≫ pullback.snd tM sκ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R₀) (A := B) (B := κ)).toRingHom) := by
    simp only [jB, Category.assoc, pullback.lift_snd, Category.comp_id]
    exact pullbackSpecIso_inv_snd R₀ B κ
  have jB'_fst : jB' ≫ pullback.fst tN sκ =
      Spec.map (CommRingCat.ofHom (algebraMap B' (B' ⊗[R₀] κ))) ≫ ι' := by
    simp only [jB', Category.assoc, pullback.lift_fst]
    rw [← Category.assoc, pullbackSpecIso_inv_fst']
  have jB'_snd : jB' ≫ pullback.snd tN sκ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R₀) (A := B') (B := κ)).toRingHom) := by
    simp only [jB', Category.assoc, pullback.lift_snd, Category.comp_id]
    exact pullbackSpecIso_inv_snd R₀ B' κ

  have hxr : x ∈ Set.range jB.base := by
    have hm : x ∈ Set.range (pullback.map _ _ _ _ ι (𝟙 _) (𝟙 _) eB₁ eB₂).base := by
      rw [Scheme.Pullback.range_map]
      exact ⟨hx, ⟨(pullback.snd tM sκ).base x, by simp⟩⟩
    obtain ⟨y, hy⟩ := hm
    refine ⟨(pullbackSpecIso R₀ B κ).hom.base y, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    simp only [jB, Iso.hom_inv_id_assoc]
    exact hy
  obtain ⟨q, rfl⟩ := hxr

  have hqU : q ∈ jB ⁻¹ᵁ V₀ := hxV
  obtain ⟨_, ⟨g, rfl⟩, hqg, hgU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqU (jB ⁻¹ᵁ V₀).isOpen
  let lg := Spec.map (CommRingCat.ofHom (algebraMap (B ⊗[R₀] κ) (Localization.Away g)))
  have hlg_mem : ∀ w, lg.base w ∈ PrimeSpectrum.basicOpen g := fun w => by
    have hw : PrimeSpectrum.comap (algebraMap (B ⊗[R₀] κ) (Localization.Away g)) w ∈
        Set.range (PrimeSpectrum.comap (algebraMap (B ⊗[R₀] κ) (Localization.Away g))) := ⟨w, rfl⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g] at hw
    exact hw
  have hsub : Set.range (lg ≫ jB).base ⊆ Set.range V₀.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    show jB.base (lg.base w) ∈ V₀
    exact hgU (hlg_mem w)
  let l := IsOpenImmersion.lift V₀.ι (lg ≫ jB) hsub
  have hl : l ≫ V₀.ι = lg ≫ jB := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion l := by
    have : IsOpenImmersion (l ≫ V₀.ι) := by rw [hl]; infer_instance
    exact IsOpenImmersion.of_comp l V₀.ι
  have hcmpOI : IsOpenImmersion (lg ≫ jB ≫ πκ) := by
    have : lg ≫ jB ≫ πκ = l ≫ (V₀.ι ≫ πκ) := by rw [← Category.assoc, ← hl, Category.assoc]
    rw [this]
    infer_instance

  let φκ : B' ⊗[R₀] κ →ₐ[R₀] B ⊗[R₀] κ := Algebra.TensorProduct.map φ (AlgHom.id R₀ κ)
  let ψ : B' ⊗[R₀] κ →+* Localization.Away g := (algebraMap (B ⊗[R₀] κ) (Localization.Away g)).comp φκ.toRingHom
  have hcmp : lg ≫ jB ≫ πκ = Spec.map (CommRingCat.ofHom ψ) ≫ jB' := by
    apply pullback.hom_ext
    · have h1 : (lg ≫ jB ≫ πκ) ≫ pullback.fst tN sκ =
          lg ≫ Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[R₀] κ))) ≫
            Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ι' := by
        rw [Category.assoc, Category.assoc, hπκ₁, ← Category.assoc jB, jB_fst, Category.assoc, hchart]
      have h2 : (Spec.map (CommRingCat.ofHom ψ) ≫ jB') ≫ pullback.fst tN sκ =
          Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap B' (B' ⊗[R₀] κ))) ≫ ι' := by
        rw [Category.assoc, jB'_fst]
      rw [h1, h2, ← Category.assoc, ← Category.assoc, ← Category.assoc (Spec.map (CommRingCat.ofHom ψ))]
      congr 1
      simp only [lg, ← Spec.map_comp]
      congr 1
      all_goals
        ext b
        change algebraMap (B ⊗[R₀] κ) (Localization.Away g) (algebraMap B (B ⊗[R₀] κ) (φ b)) =
          algebraMap (B ⊗[R₀] κ) (Localization.Away g) (φκ (algebraMap B' (B' ⊗[R₀] κ) b))
        simp [φκ, Algebra.TensorProduct.algebraMap_apply]
    · have h1 : (lg ≫ jB ≫ πκ) ≫ pullback.snd tN sκ =
          lg ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R₀) (A := B) (B := κ)).toRingHom) := by
        rw [Category.assoc, Category.assoc, hπκ₂, jB_snd]
      have h2 : (Spec.map (CommRingCat.ofHom ψ) ≫ jB') ≫ pullback.snd tN sκ =
          Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R₀) (A := B') (B := κ)).toRingHom) := by
        rw [Category.assoc, jB'_snd]
      rw [h1, h2]
      simp only [lg, ← Spec.map_comp]
      congr 1
      all_goals
        ext k
        change algebraMap (B ⊗[R₀] κ) (Localization.Away g) ((1 : B) ⊗ₜ k) =
          algebraMap (B ⊗[R₀] κ) (Localization.Away g) (φκ ((1 : B') ⊗ₜ k))
        simp [φκ]
  have hψOI : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ)) := by
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ) ≫ jB') := by rw [← hcmp]; exact hcmpOI
    exact IsOpenImmersion.of_comp _ jB'
  have hψ : ψ.FormallyUnramified := by
    have : FormallyUnramified (Spec.map (CommRingCat.ofHom ψ)) := inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mp this

  obtain ⟨f, hf, hfU⟩ := exists_formallyUnramified_away_of_baseChange φ hφ q.asIdeal g hqg hψ
  refine ⟨_, Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away f))) ≫ ι, inferInstance, ?_, ?_⟩
  swap
  ·
    rw [Category.assoc, hchart, ← Category.assoc, ← Spec.map_comp]
    have h1 : FormallyUnramified (Spec.map (CommRingCat.ofHom φ.toRingHom ≫ CommRingCat.ofHom (algebraMap B (Localization.Away f)))) :=
      (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mpr hfU
    exact MorphismProperty.comp_mem _ _ _ h1 inferInstance

  have hpt : (pullback.fst tM sκ).base (jB.base q) =
      ι.base (PrimeSpectrum.comap (algebraMap B (B ⊗[R₀] κ)) q) := by
    rw [← Scheme.Hom.comp_apply, jB_fst, Scheme.Hom.comp_apply]
    rfl
  have hmemf : PrimeSpectrum.comap (algebraMap B (B ⊗[R₀] κ)) q ∈
      Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    exact hf
  obtain ⟨w, hw⟩ := hmemf
  refine ⟨w, ?_⟩
  rw [hpt, Scheme.Hom.comp_apply, ← hw]
  rfl

end PiFibre

namespace PiFibre

variable {p : ℕ} [Fact p.Prime] {Γ Γ' : Subgroup SL(2, ℤ)} {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}

theorem fibreMap_fst (φ : SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj)) {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    XHDRLevel.fibreMap (Γ := Γ) (Γ' := Γ') φ toκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ φ.1 := by
  rw [XHDRLevel.fibreMap, pullback.lift_fst]

theorem fibreMap_snd (φ : SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj)) {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    XHDRLevel.fibreMap (Γ := Γ) (Γ' := Γ') φ toκ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [XHDRLevel.fibreMap, pullback.lift_snd, Category.comp_id]

end PiFibre

namespace PiFibre

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} [NeZero (M / p)]
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

def offComp1 : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).Opens :=
  ⟨(Set.range (𝔛.comp A hA ρ hρ 1).base)ᶜ,
    (𝔛.comp_isClosedImmersion A hA ρ hρ 1).base_closed.isClosed_range.isOpen_compl⟩

theorem mem_offComp1_iff (z : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) :
    z ∈ offComp1 𝔛 A hA ρ hρ ↔ z ∉ Set.range (𝔛.comp A hA ρ hρ 1).base := Iff.rfl

theorem isOpenImmersion_offComp1_ι_fibreMap_pi :
    IsOpenImmersion ((offComp1 𝔛 A hA ρ hρ).ι ≫
      XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓN p M H hpM) 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)) := by
  set V₀ := offComp1 𝔛 A hA ρ hρ with hV₀
  set c := 𝔛.comp A hA ρ hρ 0 with hc
  haveI : IsClosedImmersion c := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI : IsReduced (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) :=
    𝔛.fibre_reduced A hA ρ hρ
  have hcπ : c ≫ XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓN p M H hpM) 𝔛.π ((IsLocalRing.residue ↥A).comp ρ) = 𝟙 _ :=
    𝔛.comp_pi A hA ρ hρ

  haveI : Surjective (c ∣_ V₀) := by
    refine ⟨fun v => ?_⟩
    obtain ⟨v, hv⟩ := v
    have hv' : v ∉ Set.range (𝔛.comp A hA ρ hρ 1).base := hv
    obtain (⟨z, rfl⟩ | h1) := 𝔛.comp_jointly_surjective A hA ρ hρ v
    · refine ⟨⟨z, show c.base z ∈ V₀ from hv⟩, ?_⟩
      apply Subtype.ext
      exact morphismRestrict_base_coe c V₀ ⟨z, _⟩
    · exact absurd h1 hv'
  haveI : IsIso (c ∣_ V₀) := isIso_of_isClosedImmersion_of_surjective _
  have hι : V₀.ι = inv (c ∣_ V₀) ≫ (c ⁻¹ᵁ V₀).ι ≫ c := by
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  rw [hι, Category.assoc, Category.assoc, hcπ, Category.comp_id]
  infer_instance

end PiFibre

namespace PiFibre

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} [NeZero (M / p)]
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

theorem exists_opens_formallyUnramified_pi
    (z : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hz : z ∉ Set.range (𝔛.comp A hA ρ hρ 1).base) :
    ∃ V : (X p (ΓM M H) hj).Opens,
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base z ∈ V ∧
      FormallyUnramified (V.ι ≫ 𝔛.π.1) := by

  letI algM : Algebra (R p) ↥(chartAlgFin p (ΓM M H) hj) := (chartAlgFin p (ΓM M H) hj).algebra
  letI algN : Algebra (R p) ↥(chartAlgFin p (ΓN p M H hpM) hj) := (chartAlgFin p (ΓN p M H hpM) hj).algebra
  letI algMi : Algebra (R p) ↥(chartAlgInf p (ΓM M H) hj) := (chartAlgInf p (ΓM M H) hj).algebra
  letI algNi : Algebra (R p) ↥(chartAlgInf p (ΓN p M H hpM) hj) := (chartAlgInf p (ΓN p M H hpM) hj).algebra
  have hG := isOpenImmersion_offComp1_ι_fibreMap_pi 𝔛 A hA ρ hρ
  have e₁ := fibreMap_fst 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)
  have e₂ := fibreMap_snd 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)
  have hzV : z ∈ offComp1 𝔛 A hA ρ hρ := hz
  haveI := 𝔛.lfp
  haveI : LocallyOfFiniteType (toBase p (ΓM M H) hj) := inferInstance
  rcases AlgebraicCurve.TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf (R p) _ _
      ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base z)
    with hfin | hinf
  ·
    have hl : LocallyOfFiniteType (ιFin p (ΓM M H) hj ≫ toBase p (ΓM M H) hj) := inferInstance
    rw [AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase] at hl
    have hB := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hl
    have hca := AlgHom.comp_algebraMap 𝔛.iota0
    have hφ : 𝔛.iota0.toRingHom.FiniteType := by
      rw [CommRingCat.hom_ofHom, ← hca] at hB
      exact RingHom.FiniteType.of_comp_finiteType hB
    obtain ⟨W, w, hwOI, hmem, hFU⟩ := exists_formallyUnramified_away_of_isOpenImmersion_fibre 𝔛.iota0 hφ
      (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj) 𝔛.π.1 (ιFin p (ΓM M H) hj) (ιFin p (ΓN p M H hpM) hj)
      (AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase _ _ _) (AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase _ _ _)
      𝔛.pi_chart ((IsLocalRing.residue ↥A).comp ρ) _ e₁ e₂ z hfin (offComp1 𝔛 A hA ρ hρ) hzV hG
    haveI := hwOI
    refine ⟨w.opensRange, hmem, ?_⟩
    have hwe : (Scheme.Hom.isoOpensRange w).inv ≫ w = w.opensRange.ι := by
      rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
    have key : w.opensRange.ι ≫ 𝔛.π.1 = (Scheme.Hom.isoOpensRange w).inv ≫ (w ≫ 𝔛.π.1) := by
      rw [← Category.assoc, hwe]
    rw [key]
    exact MorphismProperty.comp_mem _ _ _ inferInstance hFU
  ·
    have hl : LocallyOfFiniteType (ιInf p (ΓM M H) hj ≫ toBase p (ΓM M H) hj) := inferInstance
    rw [AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase] at hl
    have hB := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hl
    have hca := AlgHom.comp_algebraMap 𝔛.iotaInf
    have hφ : 𝔛.iotaInf.toRingHom.FiniteType := by
      rw [CommRingCat.hom_ofHom, ← hca] at hB
      exact RingHom.FiniteType.of_comp_finiteType hB
    obtain ⟨W, w, hwOI, hmem, hFU⟩ := exists_formallyUnramified_away_of_isOpenImmersion_fibre 𝔛.iotaInf hφ
      (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj) 𝔛.π.1 (ιInf p (ΓM M H) hj) (ιInf p (ΓN p M H hpM) hj)
      (AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase _ _ _) (AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase _ _ _)
      𝔛.pi_chartInf ((IsLocalRing.residue ↥A).comp ρ) _ e₁ e₂ z hinf (offComp1 𝔛 A hA ρ hρ) hzV hG
    haveI := hwOI
    refine ⟨w.opensRange, hmem, ?_⟩
    have hwe : (Scheme.Hom.isoOpensRange w).inv ≫ w = w.opensRange.ι := by
      rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
    have key : w.opensRange.ι ≫ 𝔛.π.1 = (Scheme.Hom.isoOpensRange w).inv ≫ (w ≫ 𝔛.π.1) := by
      rw [← Category.assoc, hwe]
    rw [key]
    exact MorphismProperty.comp_mem _ _ _ inferInstance hFU

theorem schemeHomOver_eq_of_comp_pi_eq
    (u u' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hπ : u.1 ≫ 𝔛.π.1 = u'.1 ≫ 𝔛.π.1)
    (hsp : Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1 = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u'.1)
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (hz : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 1).base) :
    u = u' := by
  obtain ⟨V, hV, hFU⟩ := exists_opens_formallyUnramified_pi 𝔛 A hA ρ hρ _ hz

  have hx₀ : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
      (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) = u.1.base (IsLocalRing.closedPoint ↥A) := by
    rw [← Scheme.Hom.comp_apply, huκ₁, Scheme.Hom.comp_apply]
    congr 1
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue ↥A)
  rw [hx₀] at hV
  have hV' : u'.1.base (IsLocalRing.closedPoint ↥A) ∈ V := by
    have : u'.1.base (IsLocalRing.closedPoint ↥A) = u.1.base (IsLocalRing.closedPoint ↥A) := by
      have h := congrArg (fun g => g.base (IsLocalRing.closedPoint (ResidueField ↥A))) hsp
      have hcp : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))).base (IsLocalRing.closedPoint (ResidueField ↥A)) =
          IsLocalRing.closedPoint ↥A := IsLocalRing.comap_closedPoint (IsLocalRing.residue ↥A)
      simp only [Scheme.Hom.comp_apply] at h
      rw [hcp] at h
      exact h.symm
    rw [this]; exact hV

  have hsubset : ∀ (v : Spec (CommRingCat.of ↥A) ⟶ X p (ΓM M H) hj), v.base (IsLocalRing.closedPoint ↥A) ∈ V →
      Set.range v.base ⊆ Set.range V.ι.base := fun v hv => by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint t).map v.base.hom.continuous).mem_open V.2 hv
  let a := IsOpenImmersion.lift V.ι u.1 (hsubset u.1 hV)
  let b := IsOpenImmersion.lift V.ι u'.1 (hsubset u'.1 hV')
  have ha : a ≫ V.ι = u.1 := IsOpenImmersion.lift_fac _ _ _
  have hb : b ≫ V.ι = u'.1 := IsOpenImmersion.lift_fac _ _ _
  haveI := 𝔛.lfp
  haveI : LocallyOfFiniteType 𝔛.π.1 := by
    have : LocallyOfFiniteType (𝔛.π.1 ≫ toBase p (ΓN p M H hpM) hj) := by rw [𝔛.π.2]; infer_instance
    exact locallyOfFiniteType_of_comp _ (toBase p (ΓN p M H hpM) hj)
  haveI : FormallyUnramified (V.ι ≫ 𝔛.π.1) := hFU
  have hab : a = b := by
    refine unramified_sections_eq (V.ι ≫ 𝔛.π.1) a b ?_
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) ?_ ?_
    · rw [← Category.assoc, ha, ← Category.assoc, hb, hπ]
    · exact ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue ↥A)⟩
    · rw [← cancel_mono V.ι, Category.assoc, ha, Category.assoc, hb, hsp]
  apply Subtype.ext
  rw [← ha, ← hb, hab]

end PiFibre

set_option maxHeartbeats 3200000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP₀ : ∀ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P ≠ 𝔛.placeOn0 A hA ρ hρ n)

    (y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hπ : y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1)
    (hne : y' ≠ y) :

    (∃ V : (X p (ΓM M H) hj).Opens, Set.range u.1.base ⊆ (V : Set (X p (ΓM M H) hj)) ∧
      FormallyUnramified (V.ι ≫ 𝔛.π.1)) ∧
    ∃ u' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj),
      Spec.map (CommRingCat.ofHom A.subtype) ≫ u'.1 = y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ∧
      u'.1 ≫ 𝔛.π.1 = u.1 ≫ 𝔛.π.1 ∧
      Set.range u'.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) ∧
      ∃ uκ' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        uκ' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u'.1 ∧
        uκ' ≫ pullback.snd _ _ = 𝟙 _ ∧
        uκ'.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 0).base ∧
        ∃ P' : closedPoints (𝔛.Mfib A hA ρ hρ).C,
          (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P'.1 = uκ'.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∧
          qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P') =
            (𝔛.Mfib A hA ρ hρ).placeOfPoint P := by

  haveI := 𝔛.lfp
  haveI := 𝔛.flat
  haveI := 𝔛.isProper
  haveI := 𝔛.isProper0
  haveI := 𝔛.smooth0
  haveI := 𝔛.efib_iso A hA ρ hρ
  haveI hci0 : IsClosedImmersion (𝔛.comp A hA ρ hρ 0) := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI hci1 : IsClosedImmersion (𝔛.comp A hA ρ hρ 1) := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  haveI : IsReduced (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) := 𝔛.fibre_reduced A hA ρ hρ
  haveI : LocallyOfFiniteType (toBase p (ΓM M H) hj) := inferInstance
  set κ := ResidueField ↥A with hκdef
  set cp := IsLocalRing.closedPoint (ResidueField ↥A) with hcpdef
  have hinvE : ∀ z, (𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  have hinvE' : ∀ q, (inv (𝔛.efib A hA ρ hρ)).base ((𝔛.efib A hA ρ hρ).base q) = q := fun q => by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  have hcomp_pi : ∀ z, (XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓN p M H hpM) 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)).base
      ((𝔛.comp A hA ρ hρ 0).base z) = z := fun z => by
    have := congrArg (fun g => g.base z) (𝔛.comp_pi A hA ρ hρ)
    simpa [Scheme.Hom.comp_apply] using this
  have hcpA : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))).base cp = IsLocalRing.closedPoint ↥A :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue ↥A)

  have hsubset : ∀ (V : (X p (ΓM M H) hj).Opens) (v : Spec (CommRingCat.of ↥A) ⟶ X p (ΓM M H) hj),
      v.base (IsLocalRing.closedPoint ↥A) ∈ V → Set.range v.base ⊆ (V : Set (X p (ΓM M H) hj)) := fun V v hv => by
    rintro _ ⟨t, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint t).map v.base.hom.continuous).mem_open V.2 hv

  have hxu : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
      (uκ.base cp) = u.1.base (IsLocalRing.closedPoint ↥A) := by
    rw [← Scheme.Hom.comp_apply, huκ₁, Scheme.Hom.comp_apply, hcpA]
  have hx1 : uκ.base cp ∉ Set.range (𝔛.comp A hA ρ hρ 1).base := by
    rintro ⟨z₁, hz₁⟩
    have hmem : (𝔛.efib A hA ρ hρ).base P.1 ∈ Set.range (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨z₁, ?_⟩
      rw [hz₁, ← hP, Scheme.Hom.comp_apply]
    obtain ⟨n, hn⟩ := hmem
    obtain ⟨h, hh⟩ := (𝔛.node_pin A hA ρ hρ n).2
    have hPn : (⟨_, h⟩ : closedPoints (𝔛.Mfib A hA ρ hρ).C) = P :=
      Subtype.ext (by change (inv (𝔛.efib A hA ρ hρ)).base _ = P.1; rw [hn, hinvE'])
    rw [hPn] at hh
    exact hP₀ n hh

  obtain ⟨V, hV, hFU⟩ := PiFibre.exists_opens_formallyUnramified_pi 𝔛 A hA ρ hρ _ hx1
  rw [hxu] at hV
  refine ⟨⟨V, hsubset V u.1 hV, hFU⟩, ?_⟩

  set x' : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ X p (ΓM M H) hj := y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ with hx'def
  have hgen : Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom ρ) =
      Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
  have hx'base : x' ≫ toBase p (ΓM M H) hj = Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom ρ) := by
    rw [hgen, hx'def, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta,
      ← Category.assoc, y'.2, Category.id_comp]
  have hyx : y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ toBase p (ΓM M H) hj =
      Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom ρ) := by
    rw [hgen, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, y.2, Category.id_comp]
  let xK : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) :=
    pullback.lift x' (Spec.map (CommRingCat.ofHom A.subtype)) hx'base
  have hxK : xK ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))) := by
    rw [pullback.lift_snd]; rfl
  obtain ⟨σ, ⟨hσ₁, hσ₂⟩, -⟩ := PiFibre.valuative_section (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) xK hxK
  have hsubty : Spec.map (CommRingCat.ofHom A.subtype) = Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))) := rfl
  obtain ⟨u', hu'def⟩ : ∃ u' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj),
      u'.1 = σ ≫ pullback.fst _ _ :=
    ⟨⟨σ ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, ← Category.assoc, hσ₁, Category.id_comp]⟩, rfl⟩
  have hu' : Spec.map (CommRingCat.ofHom A.subtype) ≫ u'.1 = x' := by
    rw [hu'def, hsubty, ← Category.assoc, hσ₂, pullback.lift_fst]

  have hππ : u'.1 ≫ 𝔛.π.1 = u.1 ≫ 𝔛.π.1 := by
    have hb : ∀ (v : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)),
        (v.1 ≫ 𝔛.π.1) ≫ toBase p (ΓN p M H hpM) hj = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom ρ) := fun v => by
      rw [Category.assoc, 𝔛.π.2, v.2, Category.id_comp]
    have hx'N : (x' ≫ 𝔛.π.1) ≫ toBase p (ΓN p M H hpM) hj =
        Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom ρ) := by
      rw [Category.assoc, 𝔛.π.2, hx'base]
    let xN : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ pullback (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ρ)) :=
      pullback.lift (x' ≫ 𝔛.π.1) (Spec.map (CommRingCat.ofHom A.subtype)) hx'N
    have hxN : xN ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))) := by
      rw [pullback.lift_snd]; rfl
    obtain ⟨τ₀, -, huniq⟩ := PiFibre.valuative_section (pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ρ))) xN hxN
    have hsec : ∀ (v : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)),
        Spec.map (CommRingCat.ofHom A.subtype) ≫ v.1 ≫ 𝔛.π.1 = x' ≫ 𝔛.π.1 →
        pullback.lift (v.1 ≫ 𝔛.π.1) (𝟙 _) (hb v) = τ₀ := fun v hv => by
      apply huniq
      refine ⟨pullback.lift_snd _ _ _, ?_⟩
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
        exact hv
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]
        rfl
    have h1 := hsec u' (by rw [← Category.assoc, hu'])
    have h2 := hsec u (by rw [← Category.assoc, hu, Category.assoc, Category.assoc, ← hπ, hx'def, Category.assoc, Category.assoc])
    have := congrArg (· ≫ pullback.fst _ _) (h1.trans h2.symm)
    simpa only [pullback.lift_fst] using this

  have huκ'base : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u'.1) ≫ toBase p (ΓM M H) hj =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) := by
    rw [Category.assoc, u'.2, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let uκ' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) :=
    pullback.lift (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u'.1) (𝟙 _) huκ'base
  have huκ'₁ : uκ' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u'.1 := pullback.lift_fst _ _ _
  have huκ'₂ : uκ' ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have hxu' : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
      (uκ'.base cp) = u'.1.base (IsLocalRing.closedPoint ↥A) := by
    rw [← Scheme.Hom.comp_apply, huκ'₁, Scheme.Hom.comp_apply, hcpA]

  have hw₀ : uκ' ≫ XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓN p M H hpM) 𝔛.π ((IsLocalRing.residue ↥A).comp ρ) =
      uκ ≫ XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓN p M H hpM) 𝔛.π ((IsLocalRing.residue ↥A).comp ρ) := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, PiFibre.fibreMap_fst, ← Category.assoc, ← Category.assoc, huκ'₁, huκ₁,
        Category.assoc, Category.assoc, hππ]
    · rw [Category.assoc, Category.assoc, PiFibre.fibreMap_snd, huκ'₂, huκ₂]
  have hπx : (XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓN p M H hpM) 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)).base (uκ.base cp) =
      (𝔛.efib A hA ρ hρ).base P.1 := by
    rw [← hP, Scheme.Hom.comp_apply, hcomp_pi]
  have hπx' : (XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓN p M H hpM) 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)).base (uκ'.base cp) =
      (𝔛.efib A hA ρ hρ).base P.1 := by
    rw [← hπx, ← Scheme.Hom.comp_apply, hw₀, Scheme.Hom.comp_apply]

  have hx'0 : uκ'.base cp ∉ Set.range (𝔛.comp A hA ρ hρ 0).base := by
    rintro ⟨z₀, hz₀⟩
    have hz₀' : z₀ = (𝔛.efib A hA ρ hρ).base P.1 := by rw [← hcomp_pi z₀, hz₀, hπx']
    have hpt : uκ'.base cp = uκ.base cp := by rw [← hz₀, hz₀', ← Scheme.Hom.comp_apply, hP]
    have huκeq : uκ' = uκ :=
      AlgebraicGeometry.ext_of_apply_closedPoint_eq (pullback.snd _ _) huκ'₂ huκ₂ hpt
    have hspeq : Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u'.1 =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1 := by rw [← huκ'₁, ← huκ₁, huκeq]
    have huu : u' = u := PiFibre.schemeHomOver_eq_of_comp_pi_eq 𝔛 A hA ρ hρ u' u hππ hspeq uκ' huκ'₁
      (by rw [hpt]; exact hx1)
    apply hne
    apply Subtype.ext
    have h1 : y'.1 ≫ 𝔛.eeta = y.1 ≫ 𝔛.eeta := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, ← hx'def, ← hu', huu, hu]
      · rw [Category.assoc, Category.assoc, 𝔛.heeta, y.2, y'.2]
    exact (cancel_mono 𝔛.eeta).mp h1

  have hcl : IsClosed ({uκ'.base cp} : Set ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) :=
    (pointEquivClosedPoint (pullback.snd _ _) ⟨uκ', huκ'₂⟩).2
  obtain ⟨z₁, hz₁⟩ : uκ'.base cp ∈ Set.range (𝔛.comp A hA ρ hρ 1).base :=
    (𝔛.comp_jointly_surjective A hA ρ hρ (uκ'.base cp)).resolve_left hx'0
  have hz₁cl : IsClosed ({z₁} : Set _) := by
    have hpre : (𝔛.comp A hA ρ hρ 1).base ⁻¹' {uκ'.base cp} = {z₁} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h; exact (𝔛.comp A hA ρ hρ 1).isClosedEmbedding.injective (h.trans hz₁.symm)
      · rintro rfl; exact hz₁
    rw [← hpre]
    exact hcl.preimage (𝔛.comp A hA ρ hρ 1).continuous
  have hP'cl : IsClosed ({(inv (𝔛.efib A hA ρ hρ)).base z₁} : Set _) := by
    have hpre : (𝔛.efib A hA ρ hρ).base ⁻¹' {z₁} = {(inv (𝔛.efib A hA ρ hρ)).base z₁} := by
      ext q
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h; rw [← h, hinvE']
      · rintro rfl; exact hinvE z₁
    rw [← hpre]
    exact hz₁cl.preimage (𝔛.efib A hA ρ hρ).continuous
  let P' : closedPoints (𝔛.Mfib A hA ρ hρ).C := ⟨(inv (𝔛.efib A hA ρ hρ)).base z₁, hP'cl⟩
  have hP'pt : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P'.1 = uκ'.base cp := by
    rw [Scheme.Hom.comp_apply]
    show (𝔛.comp A hA ρ hρ 1).base ((𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base z₁)) = _
    rw [hinvE, hz₁]

  haveI : SmoothOfRelativeDimension 1
      (pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) := by
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have hsmM : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
      (uκ'.base cp) ∈ (toBase p (ΓM M H) hj).smoothLocus :=
    AlgebraicGeometry.mem_smoothLocus_of_not_mem_range_of_isClosedImmersion (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))
      (pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))
      (𝔛.comp A hA ρ hρ 1) (𝔛.comp A hA ρ hρ 0) (𝔛.comp_over A hA ρ hρ 1)
      (fun z => (𝔛.comp_jointly_surjective A hA ρ hρ z).symm) _ hx'0
  have hle : (toBase p (ΓM M H) hj).smoothLocus ≤ 𝔛.smoothLocus :=
    𝔛.smoothLocus_maximal _ (PiFibre.smooth_smoothLocus_ι_comp _)
  have hsm : u'.1.base (IsLocalRing.closedPoint ↥A) ∈ 𝔛.smoothLocus := by
    rw [← hxu']; exact hle hsmM

  have hplace : qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P') =
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P := by
    obtain ⟨h, hh⟩ := 𝔛.comp1_pi_place A hA ρ hρ P'
    have key : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫
        XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓN p M H hpM) 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)).base P'.1 =
        (𝔛.efib A hA ρ hρ).base P.1 := by
      rw [← Category.assoc, Scheme.Hom.comp_apply, hP'pt, hπx']
    have hPP : (⟨_, h⟩ : closedPoints (𝔛.Mfib A hA ρ hρ).C) = P :=
      Subtype.ext (by change (inv (𝔛.efib A hA ρ hρ)).base _ = P.1; rw [key, hinvE'])
    rw [hPP] at hh
    exact hh.symm
  exact ⟨u', hu', hππ, hsubset _ u'.1 hsm, uκ', huκ'₁, huκ'₂, hx'0, P', hP'pt, hplace⟩

#print axioms solution

end S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_one_frob_placeOfPoint_eq_of_comp_pi_eq_of_ne
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_one_frob_placeOfPoint_eq_of_comp_pi_eq_of_ne (solution)
