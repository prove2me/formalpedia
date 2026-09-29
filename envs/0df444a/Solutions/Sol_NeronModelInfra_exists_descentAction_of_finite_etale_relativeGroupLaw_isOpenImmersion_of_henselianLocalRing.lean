-- Prove2me | solution 1 for NeronModelInfra.exists_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/69ffee53-1aaf-5abc-98fd-c061205a30d9

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_DescentAction
import Theorems.Thm_NeronModelInfra_exists_opens_extension_of_forall_nhds_extension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension
import Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace R4W3GDDatum

section WeilExtension

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]

theorem pullbackMap_eq_genericFibreRestrict {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R)) (φ : Y ⟶ X) (hφ : φ ≫ f = g)
    (h₁ : g ≫ 𝟙 (Spec (CommRingCat.of R)) = φ ≫ f)
    (h₂ : specGenericFibreInclusion R K ≫ 𝟙 (Spec (CommRingCat.of R)) =
      𝟙 (Spec (CommRingCat.of K)) ≫ specGenericFibreInclusion R K) :
    pullback.map g (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) φ
        (𝟙 (Spec (CommRingCat.of K))) (𝟙 (Spec (CommRingCat.of R))) h₁ h₂ =
      (genericFibreRestrict R K f g ⟨φ, hφ⟩).1 :=
  (genericFibreRestrict_coe_eq_pullbackMap f g ⟨φ, hφ⟩ h₁ h₂).symm

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem base_ne_closedPoint {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (p : S) :
    (s ≫ specGenericFibreInclusion R K).base p ≠ IsLocalRing.closedPoint R := by
  intro h
  change (specGenericFibreInclusion R K).base (s.base p) = IsLocalRing.closedPoint R at h
  rw [specGenericFibreInclusion_eq] at h
  have h1 := congrArg PrimeSpectrum.asIdeal h
  change (PrimeSpectrum.comap (CommRingCat.ofHom (algebraMap R K)).hom (s.base p)).asIdeal =
    IsLocalRing.maximalIdeal R at h1
  rw [PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom] at h1
  have h2 : (s.base p).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  rw [h2, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)] at h1
  exact IsDiscreteValuationRing.not_a_field' (R := R) h1.symm

theorem specGenericFibreInclusion_ne_closedPoint (p : ↥(Spec (CommRingCat.of K))) :
    (specGenericFibreInclusion R K).base p ≠ IsLocalRing.closedPoint R := by
  have h := base_ne_closedPoint (R := R) K (𝟙 (Spec (CommRingCat.of K))) p
  rwa [Category.id_comp] at h

variable {B₁ B₂ Y : Scheme.{u}} {g₁ : B₁ ⟶ Spec (CommRingCat.of R)} {g₂ : B₂ ⟶ Spec (CommRingCat.of R)}

theorem exists_extension [Smooth g₁] [QuasiCompact g₁] [Smooth g₂] [IsSeparated g₂]
    (L₂ : RelativeGroupLaw R g₂)
    {y : Y ⟶ Spec (CommRingCat.of R)} (σ₁ : SchemeHomOver y g₁) (σ₂ : SchemeHomOver y g₂)
    [IsOpenImmersion σ₁.1]
    (hσ₁ : ∀ b : B₁, g₁.base b = IsLocalRing.closedPoint R →
      (∀ b' : B₁, b' ⤳ b → g₁.base b' = IsLocalRing.closedPoint R → b' = b) → b ∈ Set.range σ₁.1.base)
    (φK : SchemeHomOver (pullback.snd g₁ (specGenericFibreInclusion R K))
      (pullback.snd g₂ (specGenericFibreInclusion R K)))
    (hcompat : NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K g₁ y σ₁) φK =
      genericFibreRestrict R K g₂ y σ₂) :
    ∃ φ : SchemeHomOver g₁ g₂, genericFibreRestrict R K g₂ g₁ φ = φK := by
  let ι := specGenericFibreInclusion R K

  have hloc : ∀ η : B₁, g₁.base η = IsLocalRing.closedPoint R →
      (∀ b' : B₁, b' ⤳ η → g₁.base b' = IsLocalRing.closedPoint R → b' = η) →
      ∃ (U : B₁.Opens) (_ : η ∈ U) (g : SchemeHomOver (U.ι ≫ g₁) g₂),
        (genericFibreRestrict R K g₂ (U.ι ≫ g₁) g).1 =
          pullback.map (U.ι ≫ g₁) ι g₁ ι U.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ φK.1 := by
    intro η hη hmax
    obtain ⟨y₀, hy₀⟩ := hσ₁ η hη hmax
    let U : B₁.Opens := σ₁.1.opensRange
    have hηU : η ∈ U := ⟨y₀, hy₀⟩
    let l : (U : Scheme.{u}) ⟶ Y := IsOpenImmersion.lift σ₁.1 U.ι (by
      rw [Scheme.Opens.range_ι]; rintro _ ⟨x, rfl⟩; exact ⟨x, rfl⟩)
    have hl : l ≫ σ₁.1 = U.ι := IsOpenImmersion.lift_fac _ _ _
    have hly : l ≫ y = U.ι ≫ g₁ := by rw [← σ₁.2, ← Category.assoc, hl]
    let l' : SchemeHomOver (U.ι ≫ g₁) y := ⟨l, hly⟩
    have hU : (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ g₁) g₁) = NeronModelInfra.schemeHomOverComp l' σ₁ :=
      Subtype.ext hl.symm
    refine ⟨U, hηU, NeronModelInfra.schemeHomOverComp l' σ₂, ?_⟩
    rw [genericFibreRestrict_schemeHomOverComp, ← hcompat, pullbackMap_eq_genericFibreRestrict K g₁ _ U.ι rfl,
      hU, genericFibreRestrict_schemeHomOverComp]
    rfl

  obtain ⟨V, v, hVη, hVs, hvK⟩ :=
    NeronModelInfra.exists_opens_extension_of_forall_nhds_extension R K g₂ g₁ φK hloc
  obtain ⟨W, d, hd⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_opens_diagonal_difference_extension R L₂ g₁ V hVη hVs v
  obtain ⟨Φ, hΦ⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_extension_of_diagonal_difference_extension R L₂ g₁ V hVη
      hVs v W d hd

  have hgen : ∀ q : ↑(pullback g₁ ι), (pullback.fst g₁ ι).base q ∈ V := fun q =>
    hVη _ (by
      show (pullback.fst g₁ ι ≫ g₁).base q ≠ _
      rw [pullback.condition]; exact base_ne_closedPoint K _ q)
  let ℓ : pullback g₁ ι ⟶ ↑V :=
    IsOpenImmersion.lift V.ι (pullback.fst g₁ ι) (by
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hgen q)
  have hℓ : ℓ ≫ V.ι = pullback.fst g₁ ι := IsOpenImmersion.lift_fac _ _ _
  let κ : pullback g₁ ι ⟶ pullback (V.ι ≫ g₁) ι :=
    pullback.lift ℓ (pullback.snd g₁ ι) (by rw [← Category.assoc, hℓ, pullback.condition])
  have hκ1 : κ ≫ pullback.fst (V.ι ≫ g₁) ι = ℓ := pullback.lift_fst _ _ _
  have hκ2 : κ ≫ pullback.snd (V.ι ≫ g₁) ι = pullback.snd g₁ ι := pullback.lift_snd _ _ _
  have hκ : κ ≫ pullback.map (V.ι ≫ g₁) ι g₁ ι V.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.map, pullback.lift_fst, ← Category.assoc, hκ1, hℓ, Category.id_comp]
    · rw [Category.assoc, pullback.map, pullback.lift_snd, ← Category.assoc, hκ2, Category.id_comp,
        Category.comp_id]
  refine ⟨Φ, ?_⟩
  have h1 : κ ≫ (genericFibreRestrict R K g₂ (V.ι ≫ g₁) v).1 = (genericFibreRestrict R K g₂ g₁ Φ).1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, genericFibreRestrict_coe_comp_fst, genericFibreRestrict_coe_comp_fst,
        ← Category.assoc, hκ1, ← hΦ, ← Category.assoc, hℓ]
    · rw [Category.assoc, genericFibreRestrict_coe_comp_snd, genericFibreRestrict_coe_comp_snd, hκ2]
  apply Subtype.ext
  rw [← h1, hvK, ← Category.assoc, hκ, Category.id_comp]

end WeilExtension

section Base

variable (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']

noncomputable abbrev sMap : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R R'))

scoped instance etale_sMap [Algebra.Etale R R'] : Etale (sMap R R') := by
  refine HasRingHomProperty.Spec_iff.mpr ?_
  change RingHom.Etale (algebraMap R R')
  rw [RingHom.etale_algebraMap]
  infer_instance

theorem sMap_base_eq_closedPoint_iff [IsLocalRing R] [IsLocalRing R'] [Module.Finite R R']
    (p : ↥(Spec (CommRingCat.of R'))) :
    (sMap R R').base p = IsLocalRing.closedPoint R ↔ p = IsLocalRing.closedPoint R' := by
  have hcomap : ∀ q : PrimeSpectrum R', ((sMap R R').base q).asIdeal = q.asIdeal.comap (algebraMap R R') :=
    fun q => rfl
  constructor
  · intro h
    have h1 : (p.asIdeal.comap (algebraMap R R')).IsMaximal := by
      rw [← hcomap, h]
      exact IsLocalRing.maximalIdeal.isMaximal R
    have h2 : p.asIdeal.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ h1
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal h2
  · intro h
    subst h
    apply PrimeSpectrum.ext
    rw [hcomap]
    haveI : (IsLocalRing.closedPoint R').asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal R'
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)

variable {R R'}

theorem ne_closedPoint_of_comp_eq [IsLocalRing R] [IsLocalRing R'] [Module.Finite R R']
    {T : Scheme.{u}} {τ t' : T ⟶ Spec (CommRingCat.of R')}
    (hτ : t' ≫ sMap R R' = τ ≫ sMap R R') (p : T) (h : τ.base p ≠ IsLocalRing.closedPoint R') :
    t'.base p ≠ IsLocalRing.closedPoint R' := by
  intro hc
  apply h
  rw [← sMap_base_eq_closedPoint_iff R R'] at hc ⊢
  rw [← Scheme.Hom.comp_apply, ← hτ, Scheme.Hom.comp_apply]
  exact hc

end Base

section Main

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] [Algebra R R']
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (X' : X.Opens)
  {B' : Scheme.{u}} {g' : B' ⟶ Spec (CommRingCat.of R')}
  (jY' : SchemeHomOver (pullback.snd (X'.ι ≫ f) (sMap R R')) g')

noncomputable def sigma1 :
    SchemeHomOver (pullback.snd (pullback.snd (X'.ι ≫ f) (sMap R R') ≫ sMap R R') (sMap R R'))
      (pullback.snd (g' ≫ sMap R R') (sMap R R')) :=
  ⟨pullback.map _ _ _ _ jY'.1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, jY'.2])
      (by rw [Category.comp_id, Category.id_comp]),
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)⟩

noncomputable def sigma2 :
    SchemeHomOver (pullback.snd (pullback.snd (X'.ι ≫ f) (sMap R R') ≫ sMap R R') (sMap R R')) g' :=
  ⟨(DescentAction.canonical (sMap R R') (X'.ι ≫ f)).act ≫ jY'.1, by
    rw [Category.assoc, jY'.2]
    exact (DescentAction.canonical (sMap R R') (X'.ι ≫ f)).act_comp⟩

@[reassoc]
theorem sigma1_fst : (sigma1 f X' jY').1 ≫ pullback.fst _ _ = pullback.fst _ _ ≫ jY'.1 :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem sigma1_snd : (sigma1 f X' jY').1 ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem sigma2_coe : (sigma2 f X' jY').1 = DescentAction.flipMap (sMap R R') (X'.ι ≫ f) ≫ jY'.1 := rfl

theorem isPullback_sigma1 :
    IsPullback (sigma1 f X' jY').1 (pullback.fst _ _) (pullback.fst (g' ≫ sMap R R') (sMap R R')) jY'.1 := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback (g' ≫ sMap R R') (sMap R R')).flip
  convert (IsPullback.of_hasPullback (pullback.snd (X'.ι ≫ f) (sMap R R') ≫ sMap R R') (sMap R R')).flip
    using 1
  · exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  · rw [← Category.assoc, jY'.2]

scoped instance isOpenImmersion_sigma1 [IsOpenImmersion jY'.1] : IsOpenImmersion (sigma1 f X' jY').1 :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_sigma1 f X' jY').flip inferInstance

theorem mem_range_sigma1_iff (q : ↑(pullback (g' ≫ sMap R R') (sMap R R'))) :
    q ∈ Set.range (sigma1 f X' jY').1.base ↔
      (pullback.fst (g' ≫ sMap R R') (sMap R R')).base q ∈ Set.range jY'.1.base := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(pullback.fst (pullback.snd (X'.ι ≫ f) (sMap R R') ≫ sMap R R') (sMap R R')).base z, ?_⟩
    have e : ((sigma1 f X' jY').1 ≫ pullback.fst (g' ≫ sMap R R') (sMap R R')).base z =
        (pullback.fst (pullback.snd (X'.ι ≫ f) (sMap R R') ≫ sMap R R') (sMap R R') ≫ jY'.1).base z := by
      rw [sigma1_fst]
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at e
    exact e.symm
  · intro hq
    have hq' : q ∈ Set.range (pullback.fst (pullback.fst (g' ≫ sMap R R') (sMap R R')) jY'.1).base := by
      rw [Scheme.Pullback.range_fst]
      exact hq
    obtain ⟨z, hz⟩ := hq'
    refine ⟨(isPullback_sigma1 f X' jY').isoPullback.inv.base z, ?_⟩
    rw [← Scheme.Hom.comp_apply, (Iso.inv_comp_eq _).2 ((isPullback_sigma1 f X' jY').isoPullback_hom_fst).symm]
    exact hz

section Density

variable [IsLocalRing R] [IsLocalRing R'] [Module.Finite R R']

theorem mem_range_sigma1_of_ne
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (q : ↑(pullback (g' ≫ sMap R R') (sMap R R')))
    (hq : (pullback.snd (g' ≫ sMap R R') (sMap R R')).base q ≠ IsLocalRing.closedPoint R') :
    q ∈ Set.range (sigma1 f X' jY').1.base := by
  rw [mem_range_sigma1_iff]
  apply hjY'₁
  intro hc
  apply hq
  have e : (pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g' ≫ sMap R R').base q =
      (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R').base q := by
    rw [pullback.condition]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at e
  rw [← sMap_base_eq_closedPoint_iff R R' (g'.base _)] at hc
  rw [← sMap_base_eq_closedPoint_iff R R' ((pullback.snd (g' ≫ sMap R R') (sMap R R')).base q), ← e]
  exact hc

theorem mem_range_sigma1_of_maximal [Flat (sMap R R')]
    (hjY'₂ : ∀ b : B', g'.base b = IsLocalRing.closedPoint R' →
      (∀ y : B', y ⤳ b → g'.base y = IsLocalRing.closedPoint R' → y = b) → b ∈ Set.range jY'.1.base)
    (b : ↑(pullback (g' ≫ sMap R R') (sMap R R')))
    (hb : (pullback.snd (g' ≫ sMap R R') (sMap R R')).base b = IsLocalRing.closedPoint R')
    (hmax : ∀ b' : ↑(pullback (g' ≫ sMap R R') (sMap R R')), b' ⤳ b →
      (pullback.snd (g' ≫ sMap R R') (sMap R R')).base b' = IsLocalRing.closedPoint R' → b' = b) :
    b ∈ Set.range (sigma1 f X' jY').1.base := by
  rw [mem_range_sigma1_iff]

  have hcl : ∀ q : ↑(pullback (g' ≫ sMap R R') (sMap R R')),
      g'.base ((pullback.fst (g' ≫ sMap R R') (sMap R R')).base q) = IsLocalRing.closedPoint R' ↔
        (pullback.snd (g' ≫ sMap R R') (sMap R R')).base q = IsLocalRing.closedPoint R' := by
    intro q
    have e : (pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g' ≫ sMap R R').base q =
        (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R').base q := by
      rw [pullback.condition]
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at e
    rw [← sMap_base_eq_closedPoint_iff R R' (g'.base _),
      ← sMap_base_eq_closedPoint_iff R R' ((pullback.snd (g' ≫ sMap R R') (sMap R R')).base q), e]
  apply hjY'₂ _ ((hcl b).2 hb)
  intro y hy hyc
  obtain ⟨b', hb'b, hb'y⟩ := Flat.generalizingMap (pullback.fst (g' ≫ sMap R R') (sMap R R')) hy
  have hb'c : (pullback.snd (g' ≫ sMap R R') (sMap R R')).base b' = IsLocalRing.closedPoint R' := by
    rw [← hcl b', hb'y]
    exact hyc
  have := hmax b' hb'b hb'c
  subst this
  exact hb'y.symm

end Density

noncomputable def actP (act : pullback (g' ≫ sMap R R') (sMap R R') ⟶ B')
    (hact : act ≫ g' = pullback.snd (g' ≫ sMap R R') (sMap R R'))
    {T : Scheme.{u}} (τ t' : T ⟶ Spec (CommRingCat.of R')) (hτ : t' ≫ sMap R R' = τ ≫ sMap R R')
    (x : SchemeHomOver t' g') : SchemeHomOver τ g' :=
  NeronModelInfra.schemeHomOverComp
    (RelativeGroupLaw.baseChangePointOfBase (sMap R R')
      (⟨x.1, by rw [reassoc_of% x.2, hτ]⟩ : SchemeHomOver (τ ≫ sMap R R') (g' ≫ sMap R R')))
    (⟨act, hact⟩ : SchemeHomOver (pullback.snd (g' ≫ sMap R R') (sMap R R')) g')

theorem actP_coe (act : pullback (g' ≫ sMap R R') (sMap R R') ⟶ B')
    (hact : act ≫ g' = pullback.snd (g' ≫ sMap R R') (sMap R R'))
    {T : Scheme.{u}} (τ t' : T ⟶ Spec (CommRingCat.of R')) (hτ : t' ≫ sMap R R' = τ ≫ sMap R R')
    (x : SchemeHomOver t' g') :
    (actP act hact τ t' hτ x).1 = pullback.lift x.1 τ (by rw [reassoc_of% x.2, hτ]) ≫ act :=
  rfl

theorem comp_actP (act : pullback (g' ≫ sMap R R') (sMap R R') ⟶ B')
    (hact : act ≫ g' = pullback.snd (g' ≫ sMap R R') (sMap R R'))
    {T T₁ : Scheme.{u}} (ψ : T₁ ⟶ T) (τ t' : T ⟶ Spec (CommRingCat.of R'))
    (hτ : t' ≫ sMap R R' = τ ≫ sMap R R') (τ₁ t'₁ : T₁ ⟶ Spec (CommRingCat.of R'))
    (hψτ : ψ ≫ τ = τ₁) (hψt : ψ ≫ t' = t'₁) (hτ₁ : t'₁ ≫ sMap R R' = τ₁ ≫ sMap R R')
    (x : SchemeHomOver t' g') :
    GoodReductionJacobian.schemeHomOverComp ψ hψτ (actP act hact τ t' hτ x) =
      actP act hact τ₁ t'₁ hτ₁ (GoodReductionJacobian.schemeHomOverComp ψ hψt x) := by
  apply Subtype.ext
  rw [GoodReductionJacobian.schemeHomOverComp_coe, actP_coe, actP_coe, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, GoodReductionJacobian.schemeHomOverComp_coe]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hψτ]

noncomputable def xa {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (a : SchemeHomOver (t' ≫ sMap R R') (X'.ι ≫ f)) : SchemeHomOver t' g' :=
  NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap R R') a) jY'

theorem xa_coe {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (a : SchemeHomOver (t' ≫ sMap R R') (X'.ι ≫ f)) :
    (xa f X' jY' t' a).1 = pullback.lift a.1 t' a.2 ≫ jY'.1 :=
  rfl

def rebase {Z : Scheme.{u}} {z : Z ⟶ Spec (CommRingCat.of R)} {T : Scheme.{u}}
    {τ t' : T ⟶ Spec (CommRingCat.of R')} (hτ : t' ≫ sMap R R' = τ ≫ sMap R R')
    (a : SchemeHomOver (t' ≫ sMap R R') z) : SchemeHomOver (τ ≫ sMap R R') z :=
  ⟨a.1, a.2.trans hτ⟩

theorem act_xa (act : pullback (g' ≫ sMap R R') (sMap R R') ⟶ B')
    (hact : act ≫ g' = pullback.snd (g' ≫ sMap R R') (sMap R R'))
    (hP1 : (sigma1 f X' jY').1 ≫ act = (sigma2 f X' jY').1)
    {T : Scheme.{u}} (τ t' : T ⟶ Spec (CommRingCat.of R')) (hτ : t' ≫ sMap R R' = τ ≫ sMap R R')
    (a : SchemeHomOver (t' ≫ sMap R R') (X'.ι ≫ f)) :
    actP act hact τ t' hτ (xa f X' jY' t' a) = xa f X' jY' τ (rebase hτ a) := by
  apply Subtype.ext

  let z : T ⟶ pullback (pullback.snd (X'.ι ≫ f) (sMap R R') ≫ sMap R R') (sMap R R') :=
    pullback.lift (pullback.lift a.1 t' a.2) τ (by rw [pullback.lift_snd_assoc, hτ])
  have h1 : z ≫ (sigma1 f X' jY').1 =
      pullback.lift (xa f X' jY' t' a).1 τ (by rw [reassoc_of% (xa f X' jY' t' a).2, hτ]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, sigma1_fst, pullback.lift_fst_assoc, pullback.lift_fst, xa_coe]
    · rw [Category.assoc, sigma1_snd, pullback.lift_snd, pullback.lift_snd]
  have h2 : z ≫ (sigma2 f X' jY').1 = (xa f X' jY' τ (rebase hτ a)).1 := by
    rw [sigma2_coe, xa_coe, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, DescentAction.flipMap_fst, pullback.lift_fst_assoc, pullback.lift_fst,
        pullback.lift_fst]
      rfl
    · rw [Category.assoc, DescentAction.flipMap_snd, pullback.lift_snd, pullback.lift_snd]
  rw [actP_coe, ← h1, Category.assoc, hP1, h2]

section Lift

variable [IsLocalRing R] [IsLocalRing R'] [Module.Finite R R'] [IsOpenImmersion jY'.1]

theorem exists_eq_xa
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (x : SchemeHomOver t' g')
    (hgen : ∀ p : T, t'.base p ≠ IsLocalRing.closedPoint R') :
    ∃ a : SchemeHomOver (t' ≫ sMap R R') (X'.ι ≫ f), x = xa f X' jY' t' a := by
  have hrange : Set.range x.1.base ⊆ Set.range jY'.1.base := by
    rintro _ ⟨p, rfl⟩
    apply hjY'₁
    rw [← Scheme.Hom.comp_apply, x.2]
    exact hgen p
  let ℓ := IsOpenImmersion.lift jY'.1 x.1 hrange
  have hℓ : ℓ ≫ jY'.1 = x.1 := IsOpenImmersion.lift_fac _ _ _
  have hℓ₂ : ℓ ≫ pullback.snd (X'.ι ≫ f) (sMap R R') = t' := by
    rw [← x.2, ← hℓ, Category.assoc, jY'.2]
  refine ⟨⟨ℓ ≫ pullback.fst (X'.ι ≫ f) (sMap R R'), by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hℓ₂]⟩, ?_⟩
  apply Subtype.ext
  rw [xa_coe, ← hℓ]
  congr 1
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
  · rw [pullback.lift_snd, hℓ₂]

end Lift

section Pair

variable (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
  (U : (pullback f f).Opens) (hUW : U ≤ W)

theorem exists_pair_prod [IsLocalRing R]
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧
      (pullback.snd f f).base q ∈ X' ∧ m.1.base ⟨q, hUW hq⟩ ∈ X')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (hgen : ∀ p : T, t.base p ≠ IsLocalRing.closedPoint R)
    (a b : SchemeHomOver t (X'.ι ≫ f)) :
    ∃ (w : SchemeHomOver t (U.ι ≫ pullback.fst f f ≫ f)) (c : SchemeHomOver t (X'.ι ≫ f)),
      a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f ∧ b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f ∧
      c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 := by
  have hαf : (a.1 ≫ X'.ι) ≫ f = t := by rw [Category.assoc]; exact a.2
  have hβf : (b.1 ≫ X'.ι) ≫ f = t := by rw [Category.assoc]; exact b.2
  let pair : T ⟶ pullback f f := pullback.lift (a.1 ≫ X'.ι) (b.1 ≫ X'.ι) (hαf.trans hβf.symm)
  have hpair : pair ≫ pullback.fst f f ≫ f = t := by rw [pullback.lift_fst_assoc, hαf]
  have hrange : Set.range pair.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply hU₁
    rw [← Scheme.Hom.comp_apply, hpair]
    exact hgen z
  let wl : T ⟶ U := IsOpenImmersion.lift U.ι pair hrange
  have hwl : wl ≫ U.ι = pair := IsOpenImmersion.lift_fac _ _ _
  let w : SchemeHomOver t (U.ι ≫ pullback.fst f f ≫ f) := ⟨wl, by rw [reassoc_of% hwl, hpair]⟩
  have ha : a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f := by
    change _ = wl ≫ _
    rw [reassoc_of% hwl, pullback.lift_fst]
  have hb : b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f := by
    change _ = wl ≫ _
    rw [reassoc_of% hwl, pullback.lift_snd]

  let cm : T ⟶ X := w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1
  have hrangec : Set.range cm.base ⊆ Set.range X'.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hq : (U.ι.base (wl.base z)) ∈ U := by
      rw [Scheme.Opens.ι_apply]; exact (wl.base z).2
    have h3 := (hU₂ _ hq).2.2
    have hpt : ((pullback f f).homOfLE hUW).base (wl.base z) = ⟨U.ι.base (wl.base z), hUW hq⟩ := by
      apply Subtype.ext
      rw [Scheme.homOfLE_apply]
      rfl
    change m.1.base (((pullback f f).homOfLE hUW).base (wl.base z)) ∈ X'
    rw [hpt]
    exact h3
  let cl : T ⟶ X' := IsOpenImmersion.lift X'.ι cm hrangec
  have hcl : cl ≫ X'.ι = cm := IsOpenImmersion.lift_fac _ _ _
  have hwW : (w.1 ≫ (pullback f f).homOfLE hUW) ≫ W.ι ≫ pullback.fst f f ≫ f = t := by
    rw [Category.assoc, Scheme.homOfLE_ι_assoc]
    exact w.2
  let c : SchemeHomOver t (X'.ι ≫ f) := ⟨cl, by
    rw [reassoc_of% hcl]
    change (w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1) ≫ f = t
    rw [Category.assoc, Category.assoc, m.2, ← Category.assoc]
    exact hwW⟩
  exact ⟨w, c, ha, hb, hcl⟩

end Pair

section DVR

variable [IsDomain R] [IsDiscreteValuationRing R] [IsDomain R'] [IsDiscreteValuationRing R']
  [Module.Finite R R'] [Algebra.Etale R R']
  (K' : Type u) [Field K'] [Algebra R' K'] [IsFractionRing R' K']
  [Smooth f] [Smooth g'] [IsSeparated g'] [QuasiCompact g'] [IsOpenImmersion jY'.1]
  (LB' : RelativeGroupLaw R' g')

theorem fst_mem_range_sigma1
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (p : ↑(pullback (pullback.snd (g' ≫ sMap R R') (sMap R R')) (specGenericFibreInclusion R' K'))) :
    (pullback.fst (pullback.snd (g' ≫ sMap R R') (sMap R R')) (specGenericFibreInclusion R' K')).base p ∈
      Set.range (sigma1 f X' jY').1.base :=
  mem_range_sigma1_of_ne f X' jY' hjY'₁ _ (by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact specGenericFibreInclusion_ne_closedPoint (R := R') K' _)

theorem exists_phiK
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base) :
    ∃ φK : SchemeHomOver (pullback.snd (pullback.snd (g' ≫ sMap R R') (sMap R R')) (specGenericFibreInclusion R' K'))
        (pullback.snd g' (specGenericFibreInclusion R' K')),
      NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R' K' (pullback.snd (g' ≫ sMap R R') (sMap R R')) _ (sigma1 f X' jY')) φK =
        genericFibreRestrict R' K' g' _ (sigma2 f X' jY') := by
  let ℓ : pullback (pullback.snd (g' ≫ sMap R R') (sMap R R')) (specGenericFibreInclusion R' K') ⟶
      pullback (pullback.snd (X'.ι ≫ f) (sMap R R') ≫ sMap R R') (sMap R R') :=
    IsOpenImmersion.lift (sigma1 f X' jY').1
      (pullback.fst (pullback.snd (g' ≫ sMap R R') (sMap R R')) (specGenericFibreInclusion R' K')) (by
      rintro _ ⟨p, rfl⟩
      exact fst_mem_range_sigma1 f X' jY' K' hjY'₁ p)
  have hℓ : ℓ ≫ (sigma1 f X' jY').1 =
      pullback.fst (pullback.snd (g' ≫ sMap R R') (sMap R R')) (specGenericFibreInclusion R' K') :=
    IsOpenImmersion.lift_fac _ _ _
  have hcond : (ℓ ≫ (sigma2 f X' jY').1) ≫ g' =
      pullback.snd (pullback.snd (g' ≫ sMap R R') (sMap R R')) (specGenericFibreInclusion R' K') ≫
        specGenericFibreInclusion R' K' := by
    calc (ℓ ≫ (sigma2 f X' jY').1) ≫ g'
        = ℓ ≫ (sigma1 f X' jY').1 ≫ pullback.snd (g' ≫ sMap R R') (sMap R R') := by
          rw [Category.assoc, (sigma2 f X' jY').2, (sigma1 f X' jY').2]
      _ = pullback.fst (pullback.snd (g' ≫ sMap R R') (sMap R R')) (specGenericFibreInclusion R' K') ≫
            pullback.snd (g' ≫ sMap R R') (sMap R R') := by rw [← Category.assoc, hℓ]
      _ = _ := pullback.condition
  refine ⟨⟨pullback.lift (ℓ ≫ (sigma2 f X' jY').1) (pullback.snd _ _) hcond, pullback.lift_snd _ _ _⟩, ?_⟩
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, pullback.lift_fst,
      genericFibreRestrict_coe_comp_fst, ← Category.assoc]
    congr 1
    rw [← cancel_mono (sigma1 f X' jY').1, Category.assoc, hℓ, genericFibreRestrict_coe_comp_fst]
  · rw [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, pullback.lift_snd,
      genericFibreRestrict_coe_comp_snd, genericFibreRestrict_coe_comp_snd]

include K' LB' in

theorem exists_act
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (hjY'₂ : ∀ b : B', g'.base b = IsLocalRing.closedPoint R' →
      (∀ y : B', y ⤳ b → g'.base y = IsLocalRing.closedPoint R' → y = b) → b ∈ Set.range jY'.1.base) :
    ∃ Φ : SchemeHomOver (pullback.snd (g' ≫ sMap R R') (sMap R R')) g',
      (sigma1 f X' jY').1 ≫ Φ.1 = (sigma2 f X' jY').1 := by
  obtain ⟨φK, hcompat⟩ := exists_phiK f X' jY' K' hjY'₁
  obtain ⟨Φ, hΦ⟩ := exists_extension K' LB' (sigma1 f X' jY') (sigma2 f X' jY')
    (fun b hb hmax => mem_range_sigma1_of_maximal f X' jY' hjY'₂ b hb hmax) φK hcompat
  refine ⟨Φ, ?_⟩
  have h : NeronModelInfra.schemeHomOverComp (sigma1 f X' jY') Φ = sigma2 f X' jY' := by
    apply NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R' K' g'
      (pullback.snd (pullback.snd (X'.ι ≫ f) (sMap R R') ≫ sMap R R') (sMap R R'))
    rw [genericFibreRestrict_schemeHomOverComp, hΦ, hcompat]
  exact congrArg Subtype.val h

include K' in

theorem unit_act
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (act : pullback (g' ≫ sMap R R') (sMap R R') ⟶ B')
    (hact : act ≫ g' = pullback.snd (g' ≫ sMap R R') (sMap R R'))
    (hP1 : (sigma1 f X' jY').1 ≫ act = (sigma2 f X' jY').1) :
    DescentAction.unitMap (sMap R R') g' ≫ act = 𝟙 B' := by
  let U₁ : SchemeHomOver g' g' :=
    ⟨DescentAction.unitMap (sMap R R') g' ≫ act, by rw [Category.assoc, hact, DescentAction.unitMap_snd]⟩
  suffices h : U₁ = schemeHomOverId g' from congrArg Subtype.val h
  apply NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R' K' g' g'
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [genericFibreRestrict_coe_comp_fst, genericFibreRestrict_coe_comp_fst, schemeHomOverId_coe,
      Category.comp_id]
    let u := pullback.fst g' (specGenericFibreInclusion R' K')
    have hgen : ∀ p, (u ≫ g').base p ≠ IsLocalRing.closedPoint R' := fun p => by
      rw [pullback.condition, Scheme.Hom.comp_apply]
      exact specGenericFibreInclusion_ne_closedPoint (R := R') K' _
    obtain ⟨a, ha⟩ := exists_eq_xa f X' jY' hjY'₁ (u ≫ g') ⟨u, rfl⟩ hgen
    have hav : u = (xa f X' jY' (u ≫ g') a).1 := congrArg Subtype.val ha
    have key : actP act hact (u ≫ g') (u ≫ g') rfl ⟨u, rfl⟩ = xa f X' jY' (u ≫ g') (rebase rfl a) := by
      rw [ha]; exact act_xa f X' jY' act hact hP1 _ _ rfl a
    have hk : pullback.lift u (u ≫ g') (Category.assoc _ _ _).symm ≫ act = (xa f X' jY' (u ≫ g') a).1 :=
      congrArg Subtype.val key
    have hu : u ≫ DescentAction.unitMap (sMap R R') g' = pullback.lift u (u ≫ g') (Category.assoc _ _ _).symm := by
      apply pullback.hom_ext
      · rw [Category.assoc, DescentAction.unitMap_fst, Category.comp_id, pullback.lift_fst]
      · rw [Category.assoc, DescentAction.unitMap_snd, pullback.lift_snd]
    change u ≫ DescentAction.unitMap (sMap R R') g' ≫ act = u
    rw [← Category.assoc, hu, hk]
    exact hav.symm
  · rw [genericFibreRestrict_coe_comp_snd, genericFibreRestrict_coe_comp_snd]

theorem comp_actMap_act
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (act : pullback (g' ≫ sMap R R') (sMap R R') ⟶ B')
    (hact : act ≫ g' = pullback.snd (g' ≫ sMap R R') (sMap R R'))
    (hP1 : (sigma1 f X' jY').1 ≫ act = (sigma2 f X' jY').1)
    {T : Scheme.{u}}
    (u : T ⟶ pullback (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R') (sMap R R'))
    (hu : ∀ p : T, (u ≫ pullback.snd (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R') (sMap R R')).base p ≠
      IsLocalRing.closedPoint R') :
    u ≫ DescentAction.actMap act hact ≫ act = u ≫ DescentAction.proj₁₃ (sMap R R') g' ≫ act := by

  have hστ : (u ≫ pullback.fst _ _ ≫ pullback.snd (g' ≫ sMap R R') (sMap R R')) ≫ sMap R R' =
      (u ≫ pullback.snd (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R') (sMap R R')) ≫ sMap R R' := by
    simp only [Category.assoc]
    rw [pullback.condition]
  have htσ : (u ≫ pullback.fst _ _ ≫ pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g') ≫ sMap R R' =
      (u ≫ pullback.fst _ _ ≫ pullback.snd (g' ≫ sMap R R') (sMap R R')) ≫ sMap R R' := by
    simp only [Category.assoc]
    rw [pullback.condition]
  have hσg : ∀ p, (u ≫ pullback.fst _ _ ≫ pullback.snd (g' ≫ sMap R R') (sMap R R')).base p ≠
      IsLocalRing.closedPoint R' := fun p => ne_closedPoint_of_comp_eq hστ p (hu p)
  have htg : ∀ p, (u ≫ pullback.fst _ _ ≫ pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g').base p ≠
      IsLocalRing.closedPoint R' := fun p => ne_closedPoint_of_comp_eq htσ p (hσg p)

  let x₀ : SchemeHomOver (u ≫ pullback.fst _ _ ≫ pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g') g' :=
    ⟨u ≫ pullback.fst _ _ ≫ pullback.fst (g' ≫ sMap R R') (sMap R R'), by simp only [Category.assoc]⟩
  obtain ⟨a, ha⟩ := exists_eq_xa f X' jY' hjY'₁ _ x₀ htg

  have eA : ∀ h, pullback.lift x₀.1 (u ≫ pullback.fst _ _ ≫ pullback.snd (g' ≫ sMap R R') (sMap R R')) h =
      u ≫ pullback.fst _ _ := fun h => by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc]
    · rw [pullback.lift_snd, Category.assoc]
  have hA : (actP act hact _ _ htσ x₀).1 = u ≫ pullback.fst _ _ ≫ act := by
    rw [actP_coe, eA, Category.assoc]
  have eB : ∀ h, pullback.lift (actP act hact _ _ htσ x₀).1
      (u ≫ pullback.snd (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R') (sMap R R')) h =
      u ≫ DescentAction.actMap act hact := fun h => by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hA, Category.assoc, DescentAction.actMap_fst]
    · rw [pullback.lift_snd, Category.assoc, DescentAction.actMap_snd]
  have hB : (actP act hact _ _ hστ (actP act hact _ _ htσ x₀)).1 = u ≫ DescentAction.actMap act hact ≫ act := by
    rw [actP_coe, eB, Category.assoc]
  have eC : ∀ h, pullback.lift x₀.1
      (u ≫ pullback.snd (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R') (sMap R R')) h =
      u ≫ DescentAction.proj₁₃ (sMap R R') g' := fun h => by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, DescentAction.proj₁₃_fst]
    · rw [pullback.lift_snd, Category.assoc, DescentAction.proj₁₃_snd]
  have hC : (actP act hact _ _ (htσ.trans hστ) x₀).1 = u ≫ DescentAction.proj₁₃ (sMap R R') g' ≫ act := by
    rw [actP_coe, eC, Category.assoc]
  have hD : actP act hact _ _ hστ (actP act hact _ _ htσ x₀) = actP act hact _ _ (htσ.trans hστ) x₀ := by
    rw [ha, act_xa f X' jY' act hact hP1, act_xa f X' jY' act hact hP1, act_xa f X' jY' act hact hP1]
    rfl
  rw [← hB, ← hC, hD]

include K' in

theorem trans_act
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (act : pullback (g' ≫ sMap R R') (sMap R R') ⟶ B')
    (hact : act ≫ g' = pullback.snd (g' ≫ sMap R R') (sMap R R'))
    (hP1 : (sigma1 f X' jY').1 ≫ act = (sigma2 f X' jY').1) :
    DescentAction.actMap act hact ≫ act = DescentAction.proj₁₃ (sMap R R') g' ≫ act := by
  let T₁ : SchemeHomOver (pullback.snd (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R') (sMap R R')) g' :=
    ⟨DescentAction.actMap act hact ≫ act, by rw [Category.assoc, hact, DescentAction.actMap_snd]⟩
  let T₂ : SchemeHomOver (pullback.snd (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R') (sMap R R')) g' :=
    ⟨DescentAction.proj₁₃ (sMap R R') g' ≫ act, by rw [Category.assoc, hact, DescentAction.proj₁₃_snd]⟩
  suffices h : T₁ = T₂ from congrArg Subtype.val h
  apply NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R' K' g'
    (pullback.snd (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R') (sMap R R'))
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [genericFibreRestrict_coe_comp_fst, genericFibreRestrict_coe_comp_fst]
    change pullback.fst _ _ ≫ (DescentAction.actMap act hact ≫ act) =
      pullback.fst _ _ ≫ (DescentAction.proj₁₃ (sMap R R') g' ≫ act)
    apply comp_actMap_act f X' jY' hjY'₁ act hact hP1
    intro p
    rw [pullback.condition, Scheme.Hom.comp_apply]
    exact specGenericFibreInclusion_ne_closedPoint (R := R') K' _
  · rw [genericFibreRestrict_coe_comp_snd, genericFibreRestrict_coe_comp_snd]

section Mul

variable (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
  (U : (pullback f f).Opens) (hUW : U ≤ W)

theorem mul_actP_of_generic
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧
      (pullback.snd f f).base q ∈ X' ∧ m.1.base ⟨q, hUW hq⟩ ∈ X')
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (hres' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ sMap R R') (U.ι ≫ pullback.fst f f ≫ f))
        (a b c : SchemeHomOver (t' ≫ sMap R R') (X'.ι ≫ f)),
      a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
      c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
      NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap R R') c) jY' =
        LB'.mul t' (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap R R') a) jY')
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap R R') b) jY'))
    (act : pullback (g' ≫ sMap R R') (sMap R R') ⟶ B')
    (hact : act ≫ g' = pullback.snd (g' ≫ sMap R R') (sMap R R'))
    (hP1 : (sigma1 f X' jY').1 ≫ act = (sigma2 f X' jY').1)
    {T : Scheme.{u}} (τ t' : T ⟶ Spec (CommRingCat.of R')) (hτ : t' ≫ sMap R R' = τ ≫ sMap R R')
    (x y : SchemeHomOver t' g') (hgen : ∀ p : T, τ.base p ≠ IsLocalRing.closedPoint R') :
    actP act hact τ t' hτ (LB'.mul t' x y) = LB'.mul τ (actP act hact τ t' hτ x) (actP act hact τ t' hτ y) := by
  have hgen' : ∀ p : T, t'.base p ≠ IsLocalRing.closedPoint R' := fun p => ne_closedPoint_of_comp_eq hτ p (hgen p)
  have hgenR : ∀ p : T, (t' ≫ sMap R R').base p ≠ IsLocalRing.closedPoint R := fun p hp =>
    hgen' p ((sMap_base_eq_closedPoint_iff R R' _).1 (by rw [← Scheme.Hom.comp_apply]; exact hp))
  obtain ⟨a, rfl⟩ := exists_eq_xa f X' jY' hjY'₁ t' x hgen'
  obtain ⟨b, rfl⟩ := exists_eq_xa f X' jY' hjY'₁ t' y hgen'
  obtain ⟨w, c, ha, hb, hc⟩ := exists_pair_prod f X' W m U hUW hU₁ hU₂ (t' ≫ sMap R R') hgenR a b
  have H1 : xa f X' jY' t' c = LB'.mul t' (xa f X' jY' t' a) (xa f X' jY' t' b) := hres' t' w a b c ha hb hc
  have H2 : xa f X' jY' τ (rebase hτ c) = LB'.mul τ (xa f X' jY' τ (rebase hτ a)) (xa f X' jY' τ (rebase hτ b)) :=
    hres' τ (rebase hτ w) (rebase hτ a) (rebase hτ b) (rebase hτ c) ha hb hc
  rw [← H1, act_xa f X' jY' act hact hP1, act_xa f X' jY' act hact hP1, act_xa f X' jY' act hact hP1]
  exact H2

include K' in

theorem mul_actP
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧
      (pullback.snd f f).base q ∈ X' ∧ m.1.base ⟨q, hUW hq⟩ ∈ X')
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (hres' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ sMap R R') (U.ι ≫ pullback.fst f f ≫ f))
        (a b c : SchemeHomOver (t' ≫ sMap R R') (X'.ι ≫ f)),
      a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
      c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
      NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap R R') c) jY' =
        LB'.mul t' (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap R R') a) jY')
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap R R') b) jY'))
    (act : pullback (g' ≫ sMap R R') (sMap R R') ⟶ B')
    (hact : act ≫ g' = pullback.snd (g' ≫ sMap R R') (sMap R R'))
    (hP1 : (sigma1 f X' jY').1 ≫ act = (sigma2 f X' jY').1)
    {T : Scheme.{u}} (τ t' : T ⟶ Spec (CommRingCat.of R')) (hτ : t' ≫ sMap R R' = τ ≫ sMap R R')
    (x y : SchemeHomOver t' g') :
    actP act hact τ t' hτ (LB'.mul t' x y) = LB'.mul τ (actP act hact τ t' hτ x) (actP act hact τ t' hτ y) := by

  let qP := pullback.fst (pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g') g'
  let τ₀ : pullback (pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g') g' ⟶ Spec (CommRingCat.of R') :=
    qP ≫ pullback.snd (g' ≫ sMap R R') (sMap R R')
  let t₀ : pullback (pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g') g' ⟶ Spec (CommRingCat.of R') :=
    qP ≫ pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g'
  have hτ₀ : t₀ ≫ sMap R R' = τ₀ ≫ sMap R R' := by
    simp only [t₀, τ₀, Category.assoc]
    rw [pullback.condition]
  let x₀ : SchemeHomOver t₀ g' := ⟨qP ≫ pullback.fst (g' ≫ sMap R R') (sMap R R'), Category.assoc _ _ _⟩
  let y₀ : SchemeHomOver t₀ g' :=
    ⟨pullback.snd (pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g') g', pullback.condition.symm⟩

  haveI : Flat τ₀ := inferInstanceAs
    (Flat (pullback.fst (pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g') g' ≫
      pullback.snd (g' ≫ sMap R R') (sMap R R')))
  have huniv : actP act hact τ₀ t₀ hτ₀ (LB'.mul t₀ x₀ y₀) =
      LB'.mul τ₀ (actP act hact τ₀ t₀ hτ₀ x₀) (actP act hact τ₀ t₀ hτ₀ y₀) := by
    apply NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R' K' g' τ₀
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [genericFibreRestrict_coe_comp_fst, genericFibreRestrict_coe_comp_fst]
      have hg : ∀ p, (pullback.fst τ₀ (specGenericFibreInclusion R' K') ≫ τ₀).base p ≠
          IsLocalRing.closedPoint R' := fun p => by
        rw [pullback.condition, Scheme.Hom.comp_apply]
        exact specGenericFibreInclusion_ne_closedPoint (R := R') K' _
      have key := mul_actP_of_generic f X' jY' LB' W m U hUW hU₁ hU₂ hjY'₁ hres' act hact hP1
        (pullback.fst τ₀ (specGenericFibreInclusion R' K') ≫ τ₀)
        (pullback.fst τ₀ (specGenericFibreInclusion R' K') ≫ t₀)
        (by simp only [Category.assoc, hτ₀])
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst τ₀ (specGenericFibreInclusion R' K')) rfl x₀)
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst τ₀ (specGenericFibreInclusion R' K')) rfl y₀) hg
      rw [← LB'.mul_natural,
        ← comp_actP act hact (pullback.fst τ₀ (specGenericFibreInclusion R' K')) τ₀ t₀ hτ₀ _ _ rfl rfl,
        ← comp_actP act hact (pullback.fst τ₀ (specGenericFibreInclusion R' K')) τ₀ t₀ hτ₀ _ _ rfl rfl,
        ← comp_actP act hact (pullback.fst τ₀ (specGenericFibreInclusion R' K')) τ₀ t₀ hτ₀ _ _ rfl rfl,
        ← LB'.mul_natural] at key
      exact congrArg Subtype.val key
    · rw [genericFibreRestrict_coe_comp_snd, genericFibreRestrict_coe_comp_snd]

  let qx : T ⟶ pullback (g' ≫ sMap R R') (sMap R R') := pullback.lift x.1 τ (by rw [reassoc_of% x.2, hτ])
  have hqx : qx ≫ pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g' = y.1 ≫ g' := by
    simp only [qx]
    rw [pullback.lift_fst_assoc, x.2, y.2]
  let q : T ⟶ pullback (pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g') g' := pullback.lift qx y.1 hqx
  have hqτ : q ≫ τ₀ = τ := by
    simp only [τ₀, qP, q, qx]
    rw [pullback.lift_fst_assoc, pullback.lift_snd]
  have hqt : q ≫ t₀ = t' := by
    simp only [t₀, qP, q, qx]
    rw [pullback.lift_fst_assoc, pullback.lift_fst_assoc, x.2]
  have hx : GoodReductionJacobian.schemeHomOverComp q hqt x₀ = x := by
    apply Subtype.ext
    rw [GoodReductionJacobian.schemeHomOverComp_coe]
    simp only [x₀, q, qP, qx]
    rw [pullback.lift_fst_assoc, pullback.lift_fst]
  have hy : GoodReductionJacobian.schemeHomOverComp q hqt y₀ = y := by
    apply Subtype.ext
    rw [GoodReductionJacobian.schemeHomOverComp_coe]
    simp only [y₀, q]
    rw [pullback.lift_snd]
  have h1 := congrArg (GoodReductionJacobian.schemeHomOverComp q hqτ) huniv
  rw [comp_actP act hact q τ₀ t₀ hτ₀ τ t' hqτ hqt hτ, LB'.mul_natural, LB'.mul_natural,
    comp_actP act hact q τ₀ t₀ hτ₀ τ t' hqτ hqt hτ, comp_actP act hact q τ₀ t₀ hτ₀ τ t' hqτ hqt hτ, hx, hy] at h1
  exact h1

end Mul

end DVR

end Main

end R4W3GDDatum
p2m_reactivate "P2MW.S_NeronModelInfra_exists_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing.R4W3GDDatum"

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f f).base q ∈ X' ∧
      m.1.base ⟨q, hUW hq⟩ ∈ X')
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [Module.Finite R R'] [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {B' : Scheme.{u}} (g' : B' ⟶ Spec (CommRingCat.of R')) (LB' : RelativeGroupLaw R' g')
    [Smooth g'] [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    (jY' : SchemeHomOver (pullback.snd (X'.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g') [IsOpenImmersion jY'.1]
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (hjY'₂ : ∀ b : B', g'.base b = IsLocalRing.closedPoint R' →
      (∀ y : B', y ⤳ b → g'.base y = IsLocalRing.closedPoint R' → y = b) → b ∈ Set.range jY'.1.base)
    (hres' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫ pullback.fst f f ≫ f))
        (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (X'.ι ≫ f)),
      a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
      c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
      NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) c) jY' =
        LB'.mul t' (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) a) jY')
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) b) jY')) :
    ∃ A : DescentAction (Spec.map (CommRingCat.ofHom (algebraMap R R'))) g',
      pullback.map (pullback.snd (X'.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R R')))
          jY'.1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, jY'.2])
          (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
        (DescentAction.canonical (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (X'.ι ≫ f)).act ≫ jY'.1 ∧
      (∀ {T : Scheme.{u}} (τ t' : T ⟶ Spec (CommRingCat.of R'))
          (hτ : t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) = τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (x y : SchemeHomOver t' g'),
        NeronModelInfra.schemeHomOverComp
            (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R')))
              (⟨(LB'.mul t' x y).1, by rw [reassoc_of% (LB'.mul t' x y).2, hτ]⟩ :
                SchemeHomOver (τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                  (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))))
            (⟨A.act, A.act_comp⟩ : SchemeHomOver
              (pullback.snd (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g') =
          LB'.mul τ
            (NeronModelInfra.schemeHomOverComp
              (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R')))
                (⟨x.1, by rw [reassoc_of% x.2, hτ]⟩ :
                  SchemeHomOver (τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                    (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))))
              (⟨A.act, A.act_comp⟩ : SchemeHomOver
                (pullback.snd (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                  (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g'))
            (NeronModelInfra.schemeHomOverComp
              (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R')))
                (⟨y.1, by rw [reassoc_of% y.2, hτ]⟩ :
                  SchemeHomOver (τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                    (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))))
              (⟨A.act, A.act_comp⟩ : SchemeHomOver
                (pullback.snd (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                  (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g'))) := by
  obtain ⟨Φ, hP1⟩ := R4W3GDDatum.exists_act f X' jY' (FractionRing R') LB' hjY'₁ hjY'₂
  refine ⟨⟨Φ.1, Φ.2, R4W3GDDatum.unit_act f X' jY' (FractionRing R') hjY'₁ Φ.1 Φ.2 hP1,
    R4W3GDDatum.trans_act f X' jY' (FractionRing R') hjY'₁ Φ.1 Φ.2 hP1⟩, hP1, ?_⟩
  intro T τ t' hτ x y
  exact R4W3GDDatum.mul_actP f X' jY' (FractionRing R') LB' W m U hUW hU₁ hU₂ hjY'₁ hres' Φ.1 Φ.2 hP1 τ t' hτ x y

end S_NeronModelInfra_exists_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing
end P2MW
export P2MW.S_NeronModelInfra_exists_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing (solution)
