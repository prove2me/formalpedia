-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isPullback_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/44476b82-faf6-5d47-a117-eb59745cf087

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isPullback_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_iso
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian GoodReductionJacobian.RelativeGroupLaw

namespace ModelBCT

theorem descend
    {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (M : A.Modules)
    {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')} (L' : RelativeGroupLaw R' f') (M' : A'.Modules)
    (gA : A' ⟶ A) (hg : CategoryTheory.IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ)))
    (hgmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t' f'),
      (L'.mul t' x y).1 ≫ gA =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (hgpol : Nonempty ((Scheme.Modules.pullback gA).obj M ≅ M'))
    (σ : SchemeHomOver f f) (hσiso : IsIso σ.1)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))
    (hpol : ∀ s : ↥(Spec (CommRingCat.of R)), ∃ U : (Spec (CommRingCat.of R)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ.1).obj M) ≅
        (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M)) :
    ∃ σ' : SchemeHomOver f' f', IsIso σ'.1 ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t f'),
        NeronModelInfra.schemeHomOverComp (L'.mul t x y) σ' =
          L'.mul t (NeronModelInfra.schemeHomOverComp x σ') (NeronModelInfra.schemeHomOverComp y σ')) ∧
      (∀ s : ↥(Spec (CommRingCat.of R')), ∃ U : (Spec (CommRingCat.of R')).Opens, s ∈ U ∧
        Nonempty ((Scheme.Modules.pullback (f' ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ'.1).obj M') ≅
          (Scheme.Modules.pullback (f' ⁻¹ᵁ U).ι).obj M')) ∧
      σ'.1 ≫ gA = gA ≫ σ.1 := by
  haveI := hσiso
  have w : (gA ≫ σ.1) ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ) := by rw [Category.assoc, σ.2, hg.w]
  set ε : A' ⟶ A' := hg.lift (gA ≫ σ.1) f' w with hεdef
  have hε₁ : ε ≫ gA = gA ≫ σ.1 := hg.lift_fst _ _ _
  have hεf : ε ≫ f' = f' := hg.lift_snd _ _ _
  clear_value ε
  have winv : (gA ≫ inv σ.1) ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [Category.assoc, ← hg.w]
    congr 1
    rw [IsIso.inv_comp_eq, σ.2]
  have hiso : IsIso ε := by
    refine ⟨⟨hg.lift (gA ≫ inv σ.1) f' winv, ?_, ?_⟩⟩
    · refine hg.hom_ext ?_ ?_
      · rw [Category.assoc, hg.lift_fst, ← Category.assoc, hε₁, Category.assoc, IsIso.hom_inv_id,
          Category.comp_id, Category.id_comp]
      · rw [Category.assoc, hg.lift_snd, hεf, Category.id_comp]
    · refine hg.hom_ext ?_ ?_
      · rw [Category.assoc, hε₁, ← Category.assoc, hg.lift_fst, Category.assoc, IsIso.inv_hom_id,
          Category.comp_id, Category.id_comp]
      · rw [Category.assoc, hεf, hg.lift_snd, Category.id_comp]
  let σ' : SchemeHomOver f' f' := ⟨ε, hεf⟩
  refine ⟨σ', hiso, ?_, ?_, hε₁⟩
  · intro T t x y
    apply Subtype.ext
    change (L'.mul t x y).1 ≫ ε = (L'.mul t ⟨x.1 ≫ ε, _⟩ ⟨y.1 ≫ ε, _⟩).1
    refine hg.hom_ext ?_ ?_
    · rw [Category.assoc, hε₁, ← Category.assoc, hgmul, hgmul]
      have := congrArg Subtype.val (hσ (t ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩)
      simp only [NeronModelInfra.schemeHomOverComp_coe] at this
      rw [this]
      congr 2 <;> apply Subtype.ext <;>
        simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, hε₁]
    · rw [Category.assoc, hεf, (L'.mul t x y).2, (L'.mul t _ _).2]
  · intro s'
    obtain ⟨U, hsU, ⟨i⟩⟩ := hpol ((Spec.map (CommRingCat.ofHom φ)).base s')
    obtain ⟨e⟩ := hgpol
    refine ⟨Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ U, hsU, ⟨?_⟩⟩
    let W : A.Opens := f ⁻¹ᵁ U
    let W' : A'.Opens := f' ⁻¹ᵁ (Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ U)
    have hW' : W' ≤ gA ⁻¹ᵁ W := by
      intro x hx
      change (gA ≫ f).base x ∈ U
      rw [hg.w]; exact hx
    let gW := Scheme.Hom.resLE gA W W' hW'
    have hgWι : gW ≫ W.ι = W'.ι ≫ gA := Scheme.Hom.resLE_comp_ι gA hW'
    have swap : ∀ N : A.Modules, (Scheme.Modules.pullback W'.ι).obj ((Scheme.Modules.pullback gA).obj N) ≅
        (Scheme.Modules.pullback gW).obj ((Scheme.Modules.pullback W.ι).obj N) := fun N =>
      (Scheme.Modules.pullbackComp W'.ι gA).app N ≪≫ ((Scheme.Modules.pullbackCongr hgWι).app N).symm ≪≫
        ((Scheme.Modules.pullbackComp gW W.ι).app N).symm
    refine (Scheme.Modules.pullback W'.ι).mapIso ((Scheme.Modules.pullback ε).mapIso e.symm ≪≫
        (Scheme.Modules.pullbackComp ε gA).app M ≪≫ (Scheme.Modules.pullbackCongr hε₁).app M ≪≫
        ((Scheme.Modules.pullbackComp gA σ.1).app M).symm) ≪≫ ?_
    exact swap _ ≪≫ (Scheme.Modules.pullback gW).mapIso i ≪≫ (swap _).symm ≪≫
      (Scheme.Modules.pullback W'.ι).mapIso e

theorem main
    {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (hA : AbelianSchemePropertyBundle R f)
    (L : RelativeGroupLaw R f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) (hci : Scheme.Modules.ClosedImmersionBySections M f)
    (σ : SchemeHomOver f f) (hσiso : IsIso σ.1)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))
    (hpol : ∀ s : ↥(Spec (CommRingCat.of R)), ∃ U : (Spec (CommRingCat.of R)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ.1).obj M) ≅
        (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M)) :
    ∃ (A' : Scheme.{0}) (f' : A' ⟶ Spec (CommRingCat.of R')) (L' : RelativeGroupLaw R' f')
      (_ : AbelianSchemePropertyBundle R' f')
      (M' : A'.Modules) (_ : Scheme.Modules.IsInvertible M') (_ : Scheme.Modules.ClosedImmersionBySections M' f')
      (σ' : SchemeHomOver f' f') (_ : IsIso σ'.1)
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t f'),
        NeronModelInfra.schemeHomOverComp (L'.mul t x y) σ' =
          L'.mul t (NeronModelInfra.schemeHomOverComp x σ') (NeronModelInfra.schemeHomOverComp y σ'))
      (_ : ∀ s : ↥(Spec (CommRingCat.of R')), ∃ U : (Spec (CommRingCat.of R')).Opens, s ∈ U ∧
        Nonempty ((Scheme.Modules.pullback (f' ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ'.1).obj M') ≅
          (Scheme.Modules.pullback (f' ⁻¹ᵁ U).ι).obj M'))
      (p : A' ⟶ A) (hp : CategoryTheory.IsPullback p f' f (Spec.map (CommRingCat.ofHom φ))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t' f'),
        (L'.mul t' x y).1 ≫ p =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨x.1 ≫ p, by rw [Category.assoc, hp.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ p, by rw [Category.assoc, hp.w, ← Category.assoc, y.2]⟩).1) ∧
      Nonempty ((Scheme.Modules.pullback p).obj M ≅ M') ∧
      σ'.1 ≫ p = p ≫ σ.1 := by
  let ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom φ)
  let p : baseChangeScheme ι f ⟶ A := pullback.fst f ι
  have hp : CategoryTheory.IsPullback p (baseChangeStr ι f) f ι := IsPullback.of_hasPullback f ι
  have hpmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t' (baseChangeStr ι f)),
      ((L.baseChange ι).mul t' x y).1 ≫ p =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ p, by rw [Category.assoc, hp.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ p, by rw [Category.assoc, hp.w, ← Category.assoc, y.2]⟩).1 := by
    intro T t' x y
    exact congrArg Subtype.val (baseChangePointToBase_mul ι L t' x y)
  have hA' : AbelianSchemePropertyBundle R' (baseChangeStr ι f) := AbelianSchemePropertyBundle.of_isPullback hA hp
  let M' : (baseChangeScheme ι f).Modules := (Scheme.Modules.pullback p).obj M
  have hM' : Scheme.Modules.IsInvertible M' := hM.pullback p
  have hci' : Scheme.Modules.ClosedImmersionBySections M' (baseChangeStr ι f) := by
    obtain ⟨N, 𝔓, h𝔓⟩ := hci
    letI : Algebra R R' := φ.toAlgebra
    have sq : CategoryTheory.IsPullback p (baseChangeStr ι f) f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := hp
    obtain ⟨𝔓', -, -, hsq⟩ := Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback sq 𝔓
    exact ⟨N, 𝔓', MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq h𝔓⟩
  obtain ⟨σ', hσ'iso, hσ', hpol', hcomm⟩ :=
    descend φ L M (L.baseChange ι) M' p hp hpmul ⟨Iso.refl _⟩ σ hσiso hσ hpol
  exact ⟨baseChangeScheme ι f, baseChangeStr ι f, L.baseChange ι, hA', M', hM', hci', σ', hσ'iso, hσ', hpol', p, hp,
    hpmul, ⟨Iso.refl _⟩, hcomm⟩

end ModelBCT

theorem solution
    {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (hA : AbelianSchemePropertyBundle R f)
    (L : RelativeGroupLaw R f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) (hci : Scheme.Modules.ClosedImmersionBySections M f)
    (σ : SchemeHomOver f f) (hσiso : IsIso σ.1)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))
    (hpol : ∀ s : ↥(Spec (CommRingCat.of R)), ∃ U : (Spec (CommRingCat.of R)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ.1).obj M) ≅
        (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M)) :
    ∃ (A' : Scheme.{0}) (f' : A' ⟶ Spec (CommRingCat.of R')) (L' : RelativeGroupLaw R' f')
      (_ : AbelianSchemePropertyBundle R' f')
      (M' : A'.Modules) (_ : Scheme.Modules.IsInvertible M') (_ : Scheme.Modules.ClosedImmersionBySections M' f')
      (σ' : SchemeHomOver f' f') (_ : IsIso σ'.1)
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t f'),
        NeronModelInfra.schemeHomOverComp (L'.mul t x y) σ' =
          L'.mul t (NeronModelInfra.schemeHomOverComp x σ') (NeronModelInfra.schemeHomOverComp y σ'))
      (_ : ∀ s : ↥(Spec (CommRingCat.of R')), ∃ U : (Spec (CommRingCat.of R')).Opens, s ∈ U ∧
        Nonempty ((Scheme.Modules.pullback (f' ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ'.1).obj M') ≅
          (Scheme.Modules.pullback (f' ⁻¹ᵁ U).ι).obj M'))
      (p : A' ⟶ A) (hp : CategoryTheory.IsPullback p f' f (Spec.map (CommRingCat.ofHom φ))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t' f'),
        (L'.mul t' x y).1 ≫ p =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨x.1 ≫ p, by rw [Category.assoc, hp.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ p, by rw [Category.assoc, hp.w, ← Category.assoc, y.2]⟩).1) ∧
      Nonempty ((Scheme.Modules.pullback p).obj M ≅ M') ∧
      σ'.1 ≫ p = p ≫ σ.1 :=
  ModelBCT.main φ hA L M hM hci σ hσiso hσ hpol

#print axioms solution

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isPullback_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_iso
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isPullback_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_iso (solution)
