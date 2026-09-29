-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isReduced_isFinite_isClosedImmersion_forall_iff_mem_of_finite_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/28fac984-471c-5cda-8f14-82d891e07962

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isReduced_isFinite_isClosedImmersion_forall_iff_mem_of_finite_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace RedProdK1

open scoped TensorProduct

theorem formallyUnramified_of_isReduced_of_finite (K : Type u) [Field K] [PerfectField K]
    (R : Type u) [CommRing R] [Algebra K R] [Module.Finite K R] [IsReduced R] : Algebra.FormallyUnramified K R := by
  haveI : IsArtinianRing R := IsArtinianRing.of_finite K R
  haveI : ∀ I : MaximalSpectrum R, Algebra.FormallyUnramified K (R ⧸ I.asIdeal) := by
    intro I
    haveI := I.isMaximal
    letI : Field (R ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    exact Algebra.FormallyUnramified.of_isSeparable K _
  haveI : Algebra.FormallyUnramified K (∀ I : MaximalSpectrum R, R ⧸ I.asIdeal) :=
    (Algebra.FormallyUnramified.pi_iff _).mpr this
  exact Algebra.FormallyUnramified.of_equiv ((IsArtinianRing.equivPi R).restrictScalars K).symm

theorem isReduced_tensorProduct (K : Type u) [Field K] [PerfectField K]
    (R R' : Type u) [CommRing R] [CommRing R'] [Algebra K R] [Algebra K R'] [Module.Finite K R] [Module.Finite K R']
    [IsReduced R] [IsReduced R'] : IsReduced (R ⊗[K] R') := by
  haveI := formallyUnramified_of_isReduced_of_finite K R
  haveI := formallyUnramified_of_isReduced_of_finite K R'
  haveI : Algebra.FormallyUnramified K (R ⊗[K] R') := Algebra.FormallyUnramified.comp K R (R ⊗[K] R')
  exact Algebra.FormallyUnramified.isReduced_of_field K (R ⊗[K] R')

end RedProdK1

theorem isReduced_pullback_of_isFinite_of_isReduced_of_perfectField
    {K : Type u} [Field K] [PerfectField K]
    {B B' : Scheme.{u}} (g : B ⟶ Spec (CommRingCat.of K)) (g' : B' ⟶ Spec (CommRingCat.of K))
    [IsFinite g] [IsFinite g'] [IsReduced B] [IsReduced B'] :
    IsReduced ↑(pullback g g') := by
  haveI : IsAffine B := isAffine_of_isAffineHom g
  haveI : IsAffine B' := isAffine_of_isAffineHom g'

  let φ : CommRingCat.of K ⟶ Γ(B, ⊤) := Spec.preimage (B.isoSpec.inv ≫ g)
  let φ' : CommRingCat.of K ⟶ Γ(B', ⊤) := Spec.preimage (B'.isoSpec.inv ≫ g')
  have hφ : Spec.map φ = B.isoSpec.inv ≫ g := Spec.map_preimage _
  have hφ' : Spec.map φ' = B'.isoSpec.inv ≫ g' := Spec.map_preimage _
  letI : Algebra K Γ(B, ⊤) := φ.hom.toAlgebra
  letI : Algebra K Γ(B', ⊤) := φ'.hom.toAlgebra
  haveI : Module.Finite K Γ(B, ⊤) := by
    have h1 : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
    rw [IsFinite.SpecMap_iff] at h1
    exact h1
  haveI : Module.Finite K Γ(B', ⊤) := by
    have h1 : IsFinite (Spec.map φ') := by rw [hφ']; infer_instance
    rw [IsFinite.SpecMap_iff] at h1
    exact h1
  haveI : _root_.IsReduced (TensorProduct K Γ(B, ⊤) Γ(B', ⊤)) := RedProdK1.isReduced_tensorProduct K _ _

  have hg : g ≫ 𝟙 _ = B.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(B, ⊤))) := by
    rw [Category.comp_id, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, hφ, Iso.hom_inv_id_assoc]
  have hg' : g' ≫ 𝟙 _ = B'.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(B', ⊤))) := by
    rw [Category.comp_id, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, hφ', Iso.hom_inv_id_assoc]
  let e := pullback.map g g' (Spec.map (CommRingCat.ofHom (algebraMap K Γ(B, ⊤))))
    (Spec.map (CommRingCat.ofHom (algebraMap K Γ(B', ⊤)))) B.isoSpec.hom B'.isoSpec.hom (𝟙 _) hg hg' ≫
    (pullbackSpecIso K Γ(B, ⊤) Γ(B', ⊤)).hom
  haveI : IsIso e := inferInstance
  exact isReduced_of_isOpenImmersion e

namespace EtDescK1

theorem vanishingIdeal_le_ker {T Y : Scheme.{u}} [IsReduced T] (f : T ⟶ Y) (Z : TopologicalSpace.Closeds Y)
    (hf : Set.range f.base ⊆ Z) : Scheme.IdealSheafData.vanishingIdeal Z ≤ f.ker := by
  show _ ≤ Scheme.IdealSheafData.ofIdeals _
  rw [Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U s hs
  rw [RingHom.mem_ker, ← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]
  ext t
  simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro ht
  have hmem : f.base t ∈ (Scheme.IdealSheafData.vanishingIdeal Z).support := by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hf ⟨t, rfl⟩
  rw [Scheme.IdealSheafData.mem_support_iff] at hmem
  exact (Scheme.mem_zeroLocus_iff Y _ _).mp (hmem U) s hs ht

theorem exists_reduced_finite_closedImmersion_range_eq_and_lift
    {K : Type u} [Field K] {Y : Scheme.{u}} (h : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType h]
    (S : Set Y) (hS : S.Finite) (hSc : ∀ s ∈ S, IsClosed ({s} : Set Y)) :
    ∃ (B : Scheme.{u}) (i : B ⟶ Y), IsClosedImmersion i ∧ IsReduced B ∧ IsFinite (i ≫ h) ∧
      Set.range i.base = S ∧
      ∀ (T : Scheme.{u}) [IsReduced T] (f : T ⟶ Y), Set.range f.base ⊆ S → ∃ f' : T ⟶ B, f' ≫ i = f := by
  have hScl : IsClosed S := by
    have : S = ⋃ s ∈ S, {s} := by ext; simp
    rw [this]
    exact hS.isClosed_biUnion fun s hs => hSc s hs
  let Z : TopologicalSpace.Closeds Y := ⟨S, hScl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hrange : Set.range I.subschemeι.base = S := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl

  haveI hred : IsReduced I.subscheme := by
    haveI : ∀ U : I.subschemeCover.openCover.I₀, IsReduced (I.subschemeCover.openCover.X U) := by
      intro U
      haveI : _root_.IsReduced (_ ⧸ I.ideal U) := by
        rw [← Ideal.isRadical_iff_quotient_reduced]
        show ((Scheme.IdealSheafData.vanishingIdeal Z).ideal U).IsRadical
        rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
        exact PrimeSpectrum.isRadical_vanishingIdeal _
      show IsReduced (Spec (CommRingCat.of (_ ⧸ I.ideal U)))
      infer_instance
    exact IsReduced.of_openCover _ I.subschemeCover.openCover

  haveI : Finite I.subscheme := by
    have hinj : Function.Injective I.subschemeι.base := I.subschemeι.isEmbedding.injective
    haveI : Finite S := hS.to_subtype
    refine Finite.of_injective (fun b => (⟨I.subschemeι.base b, hrange ▸ ⟨b, rfl⟩⟩ : S)) ?_
    intro b₁ b₂ hb
    exact hinj (congrArg Subtype.val hb)
  haveI : QuasiCompact (I.subschemeι ≫ h) := (quasiCompact_iff_compactSpace _).mpr inferInstance
  haveI : LocallyQuasiFinite (I.subschemeι ≫ h) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ fun _ => Set.toFinite _
  haveI : IsFinite (I.subschemeι ≫ h) := IsFinite.of_locallyQuasiFinite _
  refine ⟨I.subscheme, I.subschemeι, inferInstance, hred, inferInstance, hrange, ?_⟩
  intro T _ f hf
  refine ⟨IsClosedImmersion.lift I.subschemeι f ?_, IsClosedImmersion.lift_fac _ _ _⟩
  rw [Scheme.IdealSheafData.ker_subschemeι]
  exact vanishingIdeal_le_ker f Z hf

end EtDescK1

namespace EtDescK1

theorem isClosed_singleton_base_of_comp_eq
    {K : Type u} [Field K] (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType h]
    (z : Spec (CommRingCat.of Ω) ⟶ Y) (hz : z ≫ h = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (x : Spec (CommRingCat.of Ω)) : IsClosed ({z.base x} : Set Y) := by
  haveI : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) := by
    rw [IsIntegralHom.SpecMap_iff, CommRingCat.hom_ofHom]
    exact fun a => Algebra.IsIntegral.isIntegral a
  let z' : Spec (CommRingCat.of Ω) ⟶ pullback h (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
    pullback.lift z (𝟙 _) (by rw [hz, Category.id_comp])
  have hcl : IsClosed ({z'.base x} : Set ↥(pullback h (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))) := by
    have hmem := (pointEquivClosedPoint (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))
      ⟨z', pullback.lift_snd _ _ _⟩).2
    rw [mem_closedPoints_iff, pointEquivClosedPoint_apply_coe] at hmem
    have hx : x = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    rw [hx]
    exact hmem
  have hzz : z.base x = (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).base (z'.base x) :=
    (congrArg (fun f : Spec (CommRingCat.of Ω) ⟶ Y => f.base x) (pullback.lift_fst z (𝟙 _) (by rw [hz, Category.id_comp]))).symm
  rw [hzz, ← Set.image_singleton]
  exact (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).isClosedMap _ hcl

theorem exists_algEquiv_eq_comp_of_residueField
    {K : Type u} [Field K] (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (CommRingCat.of K)) (s : Y)
    (φ φ₀ : Y.residueField s ⟶ CommRingCat.of Ω)
    (hφ : (Spec.map φ ≫ Y.fromSpecResidueField s) ≫ h = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (hφ₀ : (Spec.map φ₀ ≫ Y.fromSpecResidueField s) ≫ h = Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :
    ∃ σ : Ω ≃ₐ[K] Ω, φ = φ₀ ≫ CommRingCat.ofHom (σ : Ω →+* Ω) := by
  let ψ : CommRingCat.of K ⟶ Y.residueField s := Spec.preimage (Y.fromSpecResidueField s ≫ h)
  have hψ : Spec.map ψ = Y.fromSpecResidueField s ≫ h := Spec.map_preimage _
  letI : Algebra K (Y.residueField s) := ψ.hom.toAlgebra
  have hc : ∀ χ : Y.residueField s ⟶ CommRingCat.of Ω,
      (Spec.map χ ≫ Y.fromSpecResidueField s) ≫ h = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) →
      ∀ r : K, χ.hom (algebraMap K (Y.residueField s) r) = algebraMap K Ω r := by
    intro χ hχ r
    have h1 : Spec.map (ψ ≫ χ) = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
      rw [Spec.map_comp, hψ, ← Category.assoc, hχ]
    have h2 := congrArg (fun f => f.hom r) (Spec.map_injective h1)
    simp at h2
    exact h2
  let a : Y.residueField s →ₐ[K] Ω := ⟨φ.hom, hc φ hφ⟩
  let a₀ : Y.residueField s →ₐ[K] Ω := ⟨φ₀.hom, hc φ₀ hφ₀⟩
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  letI : Algebra (Y.residueField s) Ω := a₀.toRingHom.toAlgebra
  haveI : IsScalarTower K (Y.residueField s) Ω := IsScalarTower.of_algebraMap_eq fun r => (a₀.commutes r).symm
  let τ : Ω →ₐ[K] Ω := a.liftNormal Ω
  have hτ : ∀ y : Y.residueField s, τ (a₀ y) = a y := fun y => a.liftNormal_commutes Ω y
  let σ : Ω ≃ₐ[K] Ω := AlgEquiv.ofBijective τ (Algebra.IsAlgebraic.algHom_bijective τ)
  refine ⟨σ, CommRingCat.hom_ext (RingHom.ext fun y => ?_)⟩
  show φ.hom y = σ (φ₀.hom y)
  exact (hτ y).symm

theorem exists_algEquiv_eq_specMap_comp
    {K : Type u} [Field K] (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (CommRingCat.of K))
    (z z₀ : Spec (CommRingCat.of Ω) ⟶ Y)
    (hz : z ≫ h = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (hz₀ : z₀ ≫ h = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (hs : z.base (IsLocalRing.closedPoint Ω) = z₀.base (IsLocalRing.closedPoint Ω)) :
    ∃ σ : Ω ≃ₐ[K] Ω, z = Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ z₀ := by
  obtain ⟨⟨s, φ⟩, hφ⟩ : ∃ q : Σ y : Y, (Y.residueField y ⟶ CommRingCat.of Ω), (Scheme.SpecToEquivOfField Ω Y).symm q = z :=
    ⟨_, Equiv.symm_apply_apply _ z⟩
  obtain ⟨⟨s₀, φ₀⟩, hφ₀⟩ : ∃ q : Σ y : Y, (Y.residueField y ⟶ CommRingCat.of Ω), (Scheme.SpecToEquivOfField Ω Y).symm q = z₀ :=
    ⟨_, Equiv.symm_apply_apply _ z₀⟩
  change Spec.map φ ≫ Y.fromSpecResidueField s = z at hφ
  change Spec.map φ₀ ≫ Y.fromSpecResidueField s₀ = z₀ at hφ₀
  have hss : s = s₀ := by
    have h1 : z.base (IsLocalRing.closedPoint Ω) = s := by
      rw [← hφ]
      exact Scheme.fromSpecResidueField_apply s _
    have h2 : z₀.base (IsLocalRing.closedPoint Ω) = s₀ := by
      rw [← hφ₀]
      exact Scheme.fromSpecResidueField_apply s₀ _
    rw [← h1, ← h2, hs]
  subst hss
  obtain ⟨σ, hσ⟩ := exists_algEquiv_eq_comp_of_residueField Ω h s φ φ₀ (by rw [hφ, hz]) (by rw [hφ₀, hz₀])
  refine ⟨σ, ?_⟩
  rw [← hφ, ← hφ₀, hσ, Spec.map_comp, Category.assoc]

end EtDescK1

namespace EtDescK1

theorem inv_natural {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t
  letI := G.pointGroup t'
  let F : SchemeHomOver t f →* SchemeHomOver t' f :=
    { toFun := GoodReductionJacobian.schemeHomOverComp ψ hψ
      map_one' := G.one_natural t t' ψ hψ
      map_mul' := fun a b => G.mul_natural t t' ψ hψ a b }
  exact map_inv F x

theorem exists_specMap_eq_of_isFinite
    {K : Type u} [Field K] (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [IsFinite f] (q : X) :
    ∃ ω : Spec (CommRingCat.of Ω) ⟶ X, ω ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ∧
      ω.base (IsLocalRing.closedPoint Ω) = q := by
  haveI : IsLocallyArtinian X := IsLocallyArtinian.of_locallyQuasiFinite f
  haveI : DiscreteTopology X := IsLocallyArtinian.discreteTopology
  haveI : IsClosedImmersion (X.fromSpecResidueField q) :=
    isClosed_singleton_iff_isClosedImmersion.mp (isClosed_discrete _)
  let ψ := Spec.preimage (X.fromSpecResidueField q ≫ f)
  have hψ : Spec.map ψ = X.fromSpecResidueField q ≫ f := Spec.map_preimage _
  have hfin : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hfin
  letI : Algebra K (X.residueField q) := ψ.hom.toAlgebra
  haveI : Module.Finite K (X.residueField q) := hfin
  haveI : Algebra.IsAlgebraic K (X.residueField q) := Algebra.IsAlgebraic.of_finite K _
  let e : X.residueField q →ₐ[K] Ω := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecResidueField q, ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp, ← CommRingCat.ofHom_hom ψ, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun r => e.commutes r
  · exact Scheme.fromSpecResidueField_apply q _

theorem exists_relativeGroupLaw_of_lift
    {K : Type u} [Field K] (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K h)
    {B : Scheme.{u}} (i : B ⟶ Y) [IsClosedImmersion i] [IsReduced B] [IsFinite (i ≫ h)]
    [IsReduced (pullback (i ≫ h) (i ≫ h))]
    (hlift : ∀ (T : Scheme.{u}) [IsReduced T] (f : T ⟶ Y), Set.range f.base ⊆ Set.range i.base → ∃ f' : T ⟶ B, f' ≫ i = f)
    (hone : ∃ w : Spec (CommRingCat.of Ω) ⟶ B, w ≫ i = (L.one (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).1)
    (hmul : ∀ x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (i ≫ h),
      ∃ w : Spec (CommRingCat.of Ω) ⟶ B, w ≫ i =
        (L.mul _ (NeronModelInfra.schemeHomOverComp x ⟨i, rfl⟩) (NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩)).1)
    (hinv : ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (i ≫ h),
      ∃ w : Spec (CommRingCat.of Ω) ⟶ B, w ≫ i = (L.inv _ (NeronModelInfra.schemeHomOverComp x ⟨i, rfl⟩)).1) :
    ∃ LB : RelativeGroupLaw K (i ≫ h),
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t (i ≫ h)),
        NeronModelInfra.schemeHomOverComp (LB.mul t x y) ⟨i, rfl⟩ =
          L.mul t (NeronModelInfra.schemeHomOverComp x ⟨i, rfl⟩) (NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩) := by
  let iY : SchemeHomOver (i ≫ h) h := ⟨i, rfl⟩
  have hinj : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (a b : SchemeHomOver t (i ≫ h)),
      NeronModelInfra.schemeHomOverComp a iY = NeronModelInfra.schemeHomOverComp b iY → a = b := by
    intro T t a b hab
    apply Subtype.ext
    rw [← cancel_mono i]
    exact congrArg Subtype.val hab

  have hrange : ∀ {P : Scheme.{u}} (fP : P ⟶ Spec (CommRingCat.of K)) [IsFinite fP] (N : P ⟶ Y),
      (∀ ω : Spec (CommRingCat.of Ω) ⟶ P, ω ≫ fP = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) →
        ∃ w : Spec (CommRingCat.of Ω) ⟶ B, w ≫ i = ω ≫ N) →
      Set.range N.base ⊆ Set.range i.base := by
    intro P fP _ N hN
    rintro _ ⟨q, rfl⟩
    obtain ⟨ω, hω, hq⟩ := exists_specMap_eq_of_isFinite Ω fP q
    obtain ⟨w, hw⟩ := hN ω hω
    refine ⟨w.base (IsLocalRing.closedPoint Ω), ?_⟩
    rw [← hq]
    show (w ≫ i).base _ = (ω ≫ N).base _
    rw [hw]

  let X1 : SchemeHomOver (pullback.fst (i ≫ h) (i ≫ h) ≫ (i ≫ h)) h :=
    ⟨pullback.fst (i ≫ h) (i ≫ h) ≫ i, by rw [Category.assoc]⟩
  let X2 : SchemeHomOver (pullback.fst (i ≫ h) (i ≫ h) ≫ (i ≫ h)) h :=
    ⟨pullback.snd (i ≫ h) (i ≫ h) ≫ i, by rw [Category.assoc, ← pullback.condition]⟩
  let M := L.mul _ X1 X2
  have hMrange : Set.range M.1.base ⊆ Set.range i.base := by
    refine hrange (pullback.fst (i ≫ h) (i ≫ h) ≫ (i ≫ h)) M.1 ?_
    intro ω hω
    let x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (i ≫ h) :=
      ⟨ω ≫ pullback.fst _ _, by rw [Category.assoc]; exact hω⟩
    let y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (i ≫ h) :=
      ⟨ω ≫ pullback.snd _ _, by rw [Category.assoc, ← pullback.condition]; exact hω⟩
    obtain ⟨w, hw⟩ := hmul x y
    refine ⟨w, ?_⟩
    rw [hw]
    have hnat := congrArg Subtype.val (L.mul_natural _ _ ω hω X1 X2)
    have e1 : GoodReductionJacobian.schemeHomOverComp ω hω X1 = NeronModelInfra.schemeHomOverComp x iY :=
      Subtype.ext (Category.assoc _ _ _).symm
    have e2 : GoodReductionJacobian.schemeHomOverComp ω hω X2 = NeronModelInfra.schemeHomOverComp y iY :=
      Subtype.ext (Category.assoc _ _ _).symm
    rw [e1, e2] at hnat
    exact hnat.symm
  obtain ⟨m, hm⟩ := hlift _ M.1 hMrange

  have hErange : Set.range (L.one (𝟙 (Spec (CommRingCat.of K)))).1.base ⊆ Set.range i.base := by
    refine hrange (𝟙 _) (L.one (𝟙 _)).1 ?_
    intro ω hω
    obtain ⟨w, hw⟩ := hone
    refine ⟨w, ?_⟩
    rw [Category.comp_id] at hω
    subst hω
    rw [hw]
    exact (congrArg Subtype.val (L.one_natural (𝟙 _) _ _ (Category.comp_id _))).symm
  obtain ⟨e, he⟩ := hlift (Spec (CommRingCat.of K)) (L.one (𝟙 _)).1 hErange

  have hNrange : Set.range (L.inv (i ≫ h) iY).1.base ⊆ Set.range i.base := by
    refine hrange (i ≫ h) (L.inv (i ≫ h) iY).1 ?_
    intro ω hω
    obtain ⟨w, hw⟩ := hinv ⟨ω, hω⟩
    refine ⟨w, ?_⟩
    rw [hw]
    have hnat := congrArg Subtype.val (inv_natural L (i ≫ h) _ ω hω iY)
    have e1 : GoodReductionJacobian.schemeHomOverComp ω hω iY = NeronModelInfra.schemeHomOverComp ⟨ω, hω⟩ iY :=
      Subtype.ext rfl
    rw [e1] at hnat
    exact hnat.symm
  obtain ⟨n, hn⟩ := hlift B (L.inv (i ≫ h) iY).1 hNrange

  let mulB : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)),
      SchemeHomOver t (i ≫ h) → SchemeHomOver t (i ≫ h) → SchemeHomOver t (i ≫ h) :=
    fun t x y => ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m, by
      rw [Category.assoc, ← Category.assoc m i h, hm, M.2, ← Category.assoc, pullback.lift_fst]
      exact x.2⟩
  have homMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t (i ≫ h)),
      NeronModelInfra.schemeHomOverComp (mulB t x y) iY =
        L.mul t (NeronModelInfra.schemeHomOverComp x iY) (NeronModelInfra.schemeHomOverComp y iY) := by
    intro T t x y
    apply Subtype.ext
    show (pullback.lift x.1 y.1 _ ≫ m) ≫ i = _
    rw [Category.assoc, hm]
    have hnat := congrArg Subtype.val (L.mul_natural _ t (pullback.lift x.1 y.1 (x.2.trans y.2.symm))
      (by rw [← Category.assoc, pullback.lift_fst]; exact x.2) X1 X2)
    have e1 : GoodReductionJacobian.schemeHomOverComp (pullback.lift x.1 y.1 (x.2.trans y.2.symm))
        (by rw [← Category.assoc, pullback.lift_fst]; exact x.2) X1 = NeronModelInfra.schemeHomOverComp x iY :=
      Subtype.ext (by
        show pullback.lift x.1 y.1 _ ≫ pullback.fst _ _ ≫ i = x.1 ≫ i
        rw [← Category.assoc, pullback.lift_fst])
    have e2 : GoodReductionJacobian.schemeHomOverComp (pullback.lift x.1 y.1 (x.2.trans y.2.symm))
        (by rw [← Category.assoc, pullback.lift_fst]; exact x.2) X2 = NeronModelInfra.schemeHomOverComp y iY :=
      Subtype.ext (by
        show pullback.lift x.1 y.1 _ ≫ pullback.snd _ _ ≫ i = y.1 ≫ i
        rw [← Category.assoc, pullback.lift_snd])
    rw [e1, e2] at hnat
    exact hnat
  let oneB : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)), SchemeHomOver t (i ≫ h) :=
    fun t => ⟨t ≫ e, by rw [Category.assoc, ← Category.assoc e i h, he, (L.one _).2, Category.comp_id]⟩
  have homOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)),
      NeronModelInfra.schemeHomOverComp (oneB t) iY = L.one t := by
    intro T t
    apply Subtype.ext
    show (t ≫ e) ≫ i = (L.one t).1
    rw [Category.assoc, he]
    exact congrArg Subtype.val (L.one_natural (𝟙 _) t t (Category.comp_id t))
  let invB : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)), SchemeHomOver t (i ≫ h) → SchemeHomOver t (i ≫ h) :=
    fun t x => ⟨x.1 ≫ n, by rw [Category.assoc, ← Category.assoc n i h, hn, (L.inv (i ≫ h) iY).2]; exact x.2⟩
  have homInv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t (i ≫ h)),
      NeronModelInfra.schemeHomOverComp (invB t x) iY = L.inv t (NeronModelInfra.schemeHomOverComp x iY) := by
    intro T t x
    apply Subtype.ext
    show (x.1 ≫ n) ≫ i = _
    rw [Category.assoc, hn]
    have hnat := congrArg Subtype.val (inv_natural L (i ≫ h) t x.1 x.2 iY)
    have e1 : GoodReductionJacobian.schemeHomOverComp x.1 x.2 iY = NeronModelInfra.schemeHomOverComp x iY :=
      Subtype.ext rfl
    rw [e1] at hnat
    exact hnat
  refine ⟨{ mul := mulB, one := oneB, inv := invB, mul_assoc := ?_, one_mul := ?_, mul_one := ?_,
            inv_mul_cancel := ?_, mul_natural := ?_ }, fun t x y => homMul t x y⟩
  · intro T t x y z
    apply hinj
    rw [homMul, homMul, homMul, homMul, L.mul_assoc]
  · intro T t x
    apply hinj
    rw [homMul, homOne, L.one_mul]
  · intro T t x
    apply hinj
    rw [homMul, homOne, L.mul_one]
  · intro T t x
    apply hinj
    rw [homMul, homInv, L.inv_mul_cancel, homOne]
  · intro T T' t t' ψ hψ x y
    apply hinj
    have e1 : NeronModelInfra.schemeHomOverComp (GoodReductionJacobian.schemeHomOverComp ψ hψ (mulB t x y)) iY =
        GoodReductionJacobian.schemeHomOverComp ψ hψ (NeronModelInfra.schemeHomOverComp (mulB t x y) iY) :=
      Subtype.ext (Category.assoc _ _ _)
    rw [e1, homMul, homMul, L.mul_natural]
    congr 1

end EtDescK1

namespace EtDescK1

theorem etDesc_of_perfectField
    {K : Type u} [Field K] [PerfectField K]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (CommRingCat.of K)) [IsSeparated h] [LocallyOfFiniteType h]
    (L : RelativeGroupLaw K h)
    (Z : Set (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) h)) (hZ : Z.Finite)
    (hone : L.one _ ∈ Z)
    (hmul : ∀ x ∈ Z, ∀ y ∈ Z, L.mul _ x y ∈ Z)
    (hinv : ∀ x ∈ Z, L.inv _ x ∈ Z)
    (hgal : ∀ (σ : Ω ≃ₐ[K] Ω), ∀ z ∈ Z, ∀ z' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) h,
      z'.1 = Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ z.1 → z' ∈ Z) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of K)) (LB : RelativeGroupLaw K g) (i : SchemeHomOver g h),
      IsReduced B ∧ IsFinite g ∧ IsClosedImmersion i.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t g),
        NeronModelInfra.schemeHomOverComp (LB.mul t x y) i = L.mul t (NeronModelInfra.schemeHomOverComp x i) (NeronModelInfra.schemeHomOverComp y i)) ∧
      (∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) h,
        (∃ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) g, NeronModelInfra.schemeHomOverComp y i = z) ↔ z ∈ Z) := by
  classical

  let S : Set Y := (fun z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) h => z.1.base (IsLocalRing.closedPoint Ω)) '' Z
  have hS : S.Finite := hZ.image _
  have hSc : ∀ s ∈ S, IsClosed ({s} : Set Y) := by
    rintro _ ⟨z, -, rfl⟩
    exact EtDescK1.isClosed_singleton_base_of_comp_eq Ω h z.1 z.2 _
  obtain ⟨B, i, hci, hred, hfin, hrange, hlift⟩ :=
    EtDescK1.exists_reduced_finite_closedImmersion_range_eq_and_lift h S hS hSc
  haveI := hci
  haveI := hred
  haveI := hfin
  haveI : IsReduced (pullback (i ≫ h) (i ≫ h)) :=
    isReduced_pullback_of_isFinite_of_isReduced_of_perfectField (i ≫ h) (i ≫ h)

  have hP : ∀ (ω : Spec (CommRingCat.of Ω) ⟶ B) (hω : ω ≫ (i ≫ h) = (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))),
      (⟨ω ≫ i, by rw [Category.assoc]; exact hω⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) h) ∈ Z := by
    intro ω hω
    have hmem : (ω ≫ i).base (IsLocalRing.closedPoint Ω) ∈ S := by
      rw [← hrange]
      exact ⟨ω.base (IsLocalRing.closedPoint Ω), rfl⟩
    obtain ⟨z₀, hz₀, hs⟩ := hmem
    obtain ⟨σ, hσ⟩ := EtDescK1.exists_algEquiv_eq_specMap_comp Ω h (ω ≫ i) z₀.1
      (by rw [Category.assoc]; exact hω) z₀.2 hs.symm
    exact hgal σ z₀ hz₀ _ hσ
  have hQ : ∀ z ∈ Z, ∃ ω : Spec (CommRingCat.of Ω) ⟶ B, ω ≫ i = z.1 := by
    intro z hz
    refine hlift _ z.1 ?_
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    subst hx
    exact ⟨z, hz, rfl⟩

  rw [← hrange] at hlift
  obtain ⟨LB, hLB⟩ := EtDescK1.exists_relativeGroupLaw_of_lift Ω h L i hlift (hQ _ hone)
    (fun x y => hQ _ (hmul _ (hP x.1 x.2) _ (hP y.1 y.2))) (fun x => hQ _ (hinv _ (hP x.1 x.2)))
  refine ⟨B, i ≫ h, LB, ⟨i, rfl⟩, hred, hfin, hci, fun t x y => hLB t x y, fun z => ⟨?_, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    exact hP y.1 y.2
  · intro hz
    obtain ⟨ω, hω⟩ := hQ z hz
    refine ⟨⟨ω, ?_⟩, Subtype.ext hω⟩
    rw [← Category.assoc, hω]
    exact z.2

end EtDescK1

namespace EtDescK1

variable {k : Type u} [Field k]

theorem specMap_algebraMap_self :
    Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (CommRingCat.of k)) := by
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]; exact Spec.map_id _

theorem hψ₁ : 𝟙 (Spec (CommRingCat.of k)) ≫ 𝟙 (Spec (CommRingCat.of k)) = Spec.map (CommRingCat.ofHom (algebraMap k k)) := by
  rw [Category.id_comp, specMap_algebraMap_self]

theorem hψ₂ : 𝟙 (Spec (CommRingCat.of k)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (CommRingCat.of k)) := by
  rw [Category.id_comp, specMap_algebraMap_self]

noncomputable abbrev cv {Y : Scheme.{u}} {h : Y ⟶ Spec (CommRingCat.of k)} (z : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) h :=
  GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ₁ z

noncomputable abbrev cv' {Y : Scheme.{u}} {h : Y ⟶ Spec (CommRingCat.of k)}
    (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) h) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h :=
  GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ₂ z

@[scoped simp] theorem cv_coe {Y : Scheme.{u}} {h : Y ⟶ Spec (CommRingCat.of k)} (z : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h) :
    (cv z).1 = z.1 := Category.id_comp _
@[scoped simp] theorem cv'_coe {Y : Scheme.{u}} {h : Y ⟶ Spec (CommRingCat.of k)}
    (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) h) : (cv' z).1 = z.1 := Category.id_comp _
theorem cv'_cv {Y : Scheme.{u}} {h : Y ⟶ Spec (CommRingCat.of k)} (z : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h) :
    cv' (cv z) = z := Subtype.ext (by simp)
theorem cv_cv' {Y : Scheme.{u}} {h : Y ⟶ Spec (CommRingCat.of k)}
    (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) h) : cv (cv' z) = z := Subtype.ext (by simp)
theorem cv_injective {Y : Scheme.{u}} {h : Y ⟶ Spec (CommRingCat.of k)} :
    Function.Injective (cv (k := k) (Y := Y) (h := h)) := fun a b hab => by
  have := congrArg Subtype.val hab; simp only [cv_coe] at this; exact Subtype.ext this

end EtDescK1
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isReduced_isFinite_isClosedImmersion_forall_iff_mem_of_finite_of_isAlgClosed.EtDescK1"

open EtDescK1 in
theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated h] [LocallyOfFiniteType h]
    (L : RelativeGroupLaw k h)
    (Z : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h)) (hZ : Z.Finite)
    (hone : L.one _ ∈ Z)
    (hmul : ∀ x ∈ Z, ∀ y ∈ Z, L.mul _ x y ∈ Z)
    (hinv : ∀ x ∈ Z, L.inv _ x ∈ Z) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of k)) (LB : RelativeGroupLaw k g) (i : SchemeHomOver g h),
      IsReduced B ∧ IsFinite g ∧ IsClosedImmersion i.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
        NeronModelInfra.schemeHomOverComp (LB.mul t x y) i =
          L.mul t (NeronModelInfra.schemeHomOverComp x i) (NeronModelInfra.schemeHomOverComp y i)) ∧
      (∃ eB : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g ≃ ↥Z,
        ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g,
          ((eB y : ↥Z) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h) = NeronModelInfra.schemeHomOverComp y i) := by
  classical

  let tΩ := Spec.map (CommRingCat.ofHom (algebraMap k k))
  let Z' : Set (SchemeHomOver tΩ h) := cv '' Z
  have hZ' : Z'.Finite := hZ.image _
  have hone' : L.one tΩ ∈ Z' := ⟨L.one _, hone, L.one_natural _ _ (𝟙 _) hψ₁⟩
  have hmul' : ∀ x ∈ Z', ∀ y ∈ Z', L.mul tΩ x y ∈ Z' := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨L.mul _ x y, hmul x hx y hy, L.mul_natural _ _ (𝟙 _) hψ₁ x y⟩
  have hinv' : ∀ x ∈ Z', L.inv tΩ x ∈ Z' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨L.inv _ x, hinv x hx, EtDescK1.inv_natural L _ _ (𝟙 _) hψ₁ x⟩
  have hgal' : ∀ (σ : k ≃ₐ[k] k), ∀ z ∈ Z', ∀ z' : SchemeHomOver tΩ h,
      z'.1 = Spec.map (CommRingCat.ofHom (σ : k →+* k)) ≫ z.1 → z' ∈ Z' := by
    intro σ z hz z' hz'
    have hσ : (σ : k →+* k) = RingHom.id k := RingHom.ext fun x => by
      simpa using σ.commutes x
    rw [hσ, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at hz'
    have : z' = z := Subtype.ext hz'
    rw [this]; exact hz
  obtain ⟨B, g, LB, i, hred, hfin, hci, hhom, hpts⟩ :=
    EtDescK1.etDesc_of_perfectField k h L Z' hZ' hone' hmul' hinv' hgal'
  refine ⟨B, g, LB, i, hred, hfin, hci, hhom, ?_⟩
  haveI := hci

  let F : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g → ↥Z := fun y =>
    ⟨NeronModelInfra.schemeHomOverComp y i, by
      have hmem : cv (NeronModelInfra.schemeHomOverComp y i) ∈ Z' :=
        (hpts _).mp ⟨cv y, Subtype.ext (by simp [NeronModelInfra.schemeHomOverComp])⟩
      obtain ⟨z, hz, hzq⟩ := hmem
      rwa [← cv_injective hzq]⟩
  have hFinj : Function.Injective F := by
    intro y₁ y₂ hy
    have h1 : (NeronModelInfra.schemeHomOverComp y₁ i).1 = (NeronModelInfra.schemeHomOverComp y₂ i).1 :=
      congrArg (fun w : ↥Z => w.1.1) hy
    apply Subtype.ext
    exact (cancel_mono i.1).mp h1
  have hFsurj : Function.Surjective F := by
    rintro ⟨z, hz⟩
    obtain ⟨y', hy'⟩ := (hpts (cv z)).mpr ⟨z, hz, rfl⟩
    refine ⟨cv' y', Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hy'
    simp only [cv_coe] at this
    show (cv' y').1 ≫ i.1 = z.1
    rw [cv'_coe]; exact this
  exact ⟨Equiv.ofBijective F ⟨hFinj, hFsurj⟩, fun y => rfl⟩

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isReduced_isFinite_isClosedImmersion_forall_iff_mem_of_finite_of_isAlgClosed
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isReduced_isFinite_isClosedImmersion_forall_iff_mem_of_finite_of_isAlgClosed (solution)
