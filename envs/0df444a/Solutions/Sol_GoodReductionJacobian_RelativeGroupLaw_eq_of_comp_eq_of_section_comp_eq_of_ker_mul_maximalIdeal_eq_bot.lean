-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/3e711a55-a0b7-5bc4-b650-cec692423db6

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Mathlib
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_injective_isTangentOfPair_of_flat
import Theorems.Thm_AlgebraicGeometry_RelTangentPoints_eq_comp_zeroSection_of_thickenedPoint_comp_eq
import Theorems.Thm_AlgebraicGeometry_SmallExtension_existsUnique_isTangentOfPair_of_flat
import Theorems.Thm_IsLocalRing_exists_ringEquiv_eqLocus_tensor_trivSqZeroExt_of_flat_of_mul_maximalIdeal_eq_bot
import Theorems.Thm_AlgebraicGeometry_bijective_algebraMap_appTop_of_isProper_of_isIntegral
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

universe u

open TensorProduct

namespace K3Inf

theorem bijective_appTop_specialFibre
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsAlgClosed (ResidueField T')]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T')) [Smooth q] [IsProper q]
    (hconn : ∀ x : Spec (CommRingCat.of T'), _root_.IsConnected (q.base ⁻¹' {x}))
    {Yk : Scheme.{u}} (ik : Yk ⟶ Y) (fk : Yk ⟶ Spec (CommRingCat.of (ResidueField T')))
    (hk : IsPullback ik fk q (Spec.map (CommRingCat.ofHom (residue T')))) :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).inv ≫ fk.appTop).hom := by
  haveI : Smooth fk := MorphismProperty.of_isPullback (P := @Smooth) hk inferInstance
  haveI : IsProper fk := MorphismProperty.of_isPullback (P := @IsProper) hk inferInstance
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (residue T'))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsClosedImmersion ik := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hk.flip inferInstance
  have hpt : ∀ p : Spec (CommRingCat.of (ResidueField T')),
      (Spec.map (CommRingCat.ofHom (residue T'))).base p = closedPoint T' := fun p =>
    PrimeSpectrum.comap_residue T' p
  have hrange : Set.range (fun y => ik.base y) = q.base ⁻¹' {closedPoint T'} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      show q.base (ik.base z) ∈ ({closedPoint T'} : Set _)
      rw [← Scheme.Hom.comp_apply, hk.w, Scheme.Hom.comp_apply]
      exact hpt _
    · intro hy
      have hy' : q.base y = (Spec.map (CommRingCat.ofHom (residue T'))).base (closedPoint (ResidueField T')) := by
        rw [hpt]; exact hy
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q)
        (g := Spec.map (CommRingCat.ofHom (residue T'))) y (closedPoint (ResidueField T')) hy'
      refine ⟨hk.isoPullback.inv.base z, ?_⟩
      show (hk.isoPullback.inv ≫ ik).base z = y
      rw [IsPullback.isoPullback_inv_fst]
      exact hz
  have hfib := hconn (closedPoint T')
  haveI : PreconnectedSpace Yk := by
    constructor
    rw [← ik.isClosedEmbedding.isInducing.isPreconnected_image, Set.image_univ]
    show _root_.IsPreconnected (Set.range (fun y => ik.base y))
    rw [hrange]
    exact hfib.isPreconnected
  haveI : Nonempty Yk := by
    obtain ⟨y, hy⟩ := hfib.nonempty
    obtain ⟨z, -⟩ := ((Set.ext_iff.1 hrange) y).2 hy
    exact ⟨z⟩
  haveI : IsIntegral Yk := isIntegral_of_smooth_of_preconnectedSpace fk
  exact bijective_algebraMap_appTop_of_isProper_of_isIntegral (ResidueField T') fk

end K3Inf

namespace K3Z
open AlgebraicGeometry.SmallExtension

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
  (C : Type u) [CommRing C] [Algebra T' C]

def diagHom : C →+* pairRing I C where
  toFun c := ⟨(c, c), by rw [mem_pairRing]⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

theorem pairFst_comp_diagHom : (pairFst I C).comp (diagHom I C) = RingHom.id C := RingHom.ext fun _ => rfl
theorem pairSnd_comp_diagHom : (pairSnd I C).comp (diagHom I C) = RingHom.id C := RingHom.ext fun _ => rfl

theorem eq_const_of_isTangentOfPair_self [IsArtinianRing T']
    (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    [Module.Flat T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T')) (a : Spec (CommRingCat.of C) ⟶ Y)
    (ha : a ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (w : Spec (CommRingCat.of (thickening T' V C)) ⟶ Y) (hw : IsTangentOfPair I V ι C a a w) :
    w = Spec.map (CommRingCat.ofHom
      ((Algebra.TensorProduct.includeLeftRingHom).comp (toReduction T' C) : C →+* thickening T' V C)) ≫ a := by
  classical
  obtain ⟨w₁, -, huniq⟩ :=
    AlgebraicGeometry.SmallExtension.existsUnique_isTangentOfPair_of_flat I hI hsmall V ι hι hιI C qY a ha a ha rfl

  obtain ⟨Θ, hΘ1, hΘ2, hΘ3⟩ :=
    IsLocalRing.exists_ringEquiv_eqLocus_tensor_trivSqZeroExt_of_flat_of_mul_maximalIdeal_eq_bot I hI hsmall V ι hι hιI C
  let ϑ : pairRing I C →+* thickening T' V C :=
    (RingHom.snd C (thickening T' V C)).comp ((Subring.subtype _).comp Θ.toRingHom)
  have hϑ : IsSchlessingerMap I V ι C ϑ := ⟨fun a ha => hΘ2 a ha, fun v c h => hΘ3 v c h⟩
  have hconst : IsTangentOfPair I V ι C a a (Spec.map (CommRingCat.ofHom
      ((Algebra.TensorProduct.includeLeftRingHom).comp (toReduction T' C) : C →+* thickening T' V C)) ≫ a) := by
    refine ⟨ϑ, hϑ, Spec.map (CommRingCat.ofHom (diagHom I C)) ≫ a, ?_, ?_, ?_⟩
    · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pairFst_comp_diagHom,
        CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pairSnd_comp_diagHom,
        CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      apply RingHom.ext
      intro c
      show (Algebra.TensorProduct.includeLeftRingHom) (toReduction T' C c) = ϑ ⟨(c, c), _⟩
      rw [hϑ.1 c]
      rfl
  exact (huniq w hw).trans (huniq _ hconst).symm

end K3Z

theorem K3_core
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
    {T : Type u} [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (I : Ideal T') (hIπ : RingHom.ker π = I) (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module.Finite (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T'))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (g : A₀ ⟶ A)
    (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (L₀ : RelativeGroupLaw T f₀)
    {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T')) [Smooth q] [IsProper q]
    (hconn : ∀ x : Spec (CommRingCat.of T'), _root_.IsConnected (q.base ⁻¹' {x}))
    {Y₀ : Scheme.{u}} (i₀ : Y₀ ⟶ Y) (q₀ : Y₀ ⟶ Spec (CommRingCat.of T))
    (h₀ : IsPullback i₀ q₀ q (Spec.map (CommRingCat.ofHom π)))
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of T'))) q)
    (u v : SchemeHomOver q f) (hred : i₀ ≫ u.1 = i₀ ≫ v.1) (hsec : s.1 ≫ u.1 = s.1 ≫ v.1) :
    u = v := by
  classical

  let rT : CommRingCat.of T' ⟶ CommRingCat.of (ResidueField T') := CommRingCat.ofHom (residue T')
  let Yk : Scheme.{u} := pullback q (Spec.map rT)
  let ik : Yk ⟶ Y := pullback.fst q (Spec.map rT)
  let fk : Yk ⟶ Spec (CommRingCat.of (ResidueField T')) := pullback.snd q (Spec.map rT)
  have hk : IsPullback ik fk q (Spec.map rT) := IsPullback.of_hasPullback q (Spec.map rT)
  let Z : Scheme.{u} := pullback fk (SquareZero.toBase (ResidueField T') V)
  let q₁ : Z ⟶ Yk := pullback.fst fk (SquareZero.toBase (ResidueField T') V)
  let q₂ : Z ⟶ SquareZero.spec (ResidueField T') V := pullback.snd fk (SquareZero.toBase (ResidueField T') V)
  have hZ : IsPullback q₁ q₂ fk (SquareZero.toBase (ResidueField T') V) := IsPullback.of_hasPullback _ _

  let e : (T' ⧸ I) ≃+* T := (Ideal.quotEquivOfEq hIπ.symm).trans (RingHom.quotientKerEquivOfSurjective hπ)
  have he : ∀ a : T', e (Ideal.Quotient.mk I a) = π a := by
    intro a
    show RingHom.quotientKerEquivOfSurjective hπ (Ideal.quotEquivOfEq hIπ.symm (Ideal.Quotient.mk I a)) = π a
    rw [Ideal.quotEquivOfEq_mk]
    exact RingHom.kerLift_mk π a
  have heπ : e.toRingHom.comp (Ideal.Quotient.mk I) = π := RingHom.ext he
  let eS : Spec (CommRingCat.of T) ≅ Spec (CommRingCat.of (T' ⧸ I)) := Scheme.Spec.mapIso e.toCommRingCatIso.op
  have heS : eS.hom = Spec.map (CommRingCat.ofHom e.toRingHom) := rfl
  have hπfac : Spec.map (CommRingCat.ofHom π) = eS.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
    rw [heS, ← Spec.map_comp, ← CommRingCat.ofHom_comp, heπ]
  have h₀' : IsPullback i₀ (q₀ ≫ eS.hom) q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsPullback.of_iso h₀ (Iso.refl _) (Iso.refl _) eS (Iso.refl _) (by simp) (by simp) (by simp)
      (by rw [Iso.refl_hom, Category.comp_id, hπfac])

  obtain ⟨Φ, hΦinj, hΦu, hΦnat, hΦchart⟩ :=
    AlgebraicGeometry.SmallExtension.exists_injective_isTangentOfPair_of_flat I hI hsmall V ι hι hιI q i₀ (q₀ ≫ eS.hom) h₀'
      ik fk hk q₁ q₂ hZ
  let vv : {v' : Y ⟶ A // v' ≫ f = q ∧ i₀ ≫ v' = i₀ ≫ u.1} := ⟨v.1, v.2, hred.symm⟩
  set w : Z ⟶ A := (Φ f u.1 u.2 vv).1 with hwdef
  have hw0 : SquareZero.zeroSection V fk q₁ q₂ hZ ≫ w = ik ≫ u.1 := (Φ f u.1 u.2 vv).2
  suffices key : w = q₁ ≫ ik ≫ u.1 by
    have e : Φ f u.1 u.2 vv = Φ f u.1 u.2 ⟨u.1, u.2, rfl⟩ := by
      apply Subtype.ext
      rw [hΦu f u.1 u.2]
      exact key
    have e2 := congrArg Subtype.val (hΦinj f u.1 u.2 e)
    apply Subtype.ext
    exact e2.symm

  have hwf : w ≫ f = q₁ ≫ fk ≫ Spec.map rT := by
    have h1 := hΦnat f (𝟙 _) f (Category.comp_id f) u.1 u.2 vv
    have h3 : ∀ (huf : (u.1 ≫ f) ≫ 𝟙 _ = q)
        (vv' : {v' : Y ⟶ Spec (CommRingCat.of T') // v' ≫ 𝟙 _ = q ∧ i₀ ≫ v' = i₀ ≫ (u.1 ≫ f)}),
        (Φ (𝟙 _) (u.1 ≫ f) huf vv').1 = q₁ ≫ ik ≫ (u.1 ≫ f) := by
      intro huf vv'
      have : vv' = ⟨u.1 ≫ f, huf, rfl⟩ := by
        apply Subtype.ext
        show vv'.1 = u.1 ≫ f
        rw [← Category.comp_id vv'.1, vv'.2.1, u.2]
      rw [this]
      exact hΦu _ _ _
    rw [h3] at h1
    rw [hwdef, ← h1, u.2, hk.w]

  have hIker : ∀ a ∈ I, residue T' a = 0 := fun a ha => (residue_eq_zero_iff a).mpr (hI ha)
  let rk : T →+* ResidueField T' := (Ideal.Quotient.lift I (residue T') hIker).comp e.symm.toRingHom
  have hrk : rk.comp π = residue T' := by
    apply RingHom.ext
    intro a
    show Ideal.Quotient.lift I (residue T') hIker (e.symm (π a)) = residue T' a
    rw [← he a, RingEquiv.symm_apply_apply]
    rfl
  let ιk : Spec (CommRingCat.of (ResidueField T')) ⟶ Spec (CommRingCat.of T) := Spec.map (CommRingCat.ofHom rk)
  have hιk : ιk ≫ Spec.map (CommRingCat.ofHom π) = Spec.map rT := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hrk]
  let zk : Z ⟶ Spec (CommRingCat.of (ResidueField T')) := q₁ ≫ fk
  have hzk : zk = q₂ ≫ SquareZero.toBase (ResidueField T') V := hZ.w
  let w₀' : Z ⟶ A₀ := hg.lift w (zk ≫ ιk) (by rw [hwf, Category.assoc, Category.assoc, hιk])
  have hw₀'g : w₀' ≫ g = w := hg.lift_fst _ _ _
  have hw₀'f : w₀' ≫ f₀ = zk ≫ ιk := hg.lift_snd _ _ _
  let Ak : Scheme.{u} := RelativeGroupLaw.baseChangeScheme ιk f₀
  let xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T')) := RelativeGroupLaw.baseChangeStr ιk f₀
  let Lk : RelativeGroupLaw (ResidueField T') xk := L₀.baseChange ιk
  let w₀ : Z ⟶ Ak := pullback.lift w₀' zk hw₀'f
  have hw₀x : w₀ ≫ xk = q₂ ≫ SquareZero.toBase (ResidueField T') V := by
    rw [← hzk]; exact pullback.lift_snd _ _ _
  let jA : Ak ⟶ A := pullback.fst f₀ ιk ≫ g
  have hjw : w₀ ≫ jA = w := by
    rw [← Category.assoc, pullback.lift_fst, hw₀'g]

  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom π)) := IsClosedImmersion.spec_of_surjective _ hπ
  haveI : IsClosedImmersion g := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hg.flip inferInstance
  have hrk_surj : Function.Surjective rk := by
    apply Function.Surjective.of_comp (g := π)
    show Function.Surjective (rk.comp π)
    rw [hrk]; exact Ideal.Quotient.mk_surjective
  haveI : IsClosedImmersion ιk := IsClosedImmersion.spec_of_surjective _ hrk_surj
  haveI : IsClosedImmersion (pullback.fst f₀ ιk) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (IsPullback.of_hasPullback f₀ ιk).flip inferInstance
  haveI : Mono jA := mono_comp _ _

  let sk : Spec (CommRingCat.of (ResidueField T')) ⟶ Yk :=
    hk.lift (Spec.map rT ≫ s.1) (𝟙 _) (by rw [Category.assoc, s.2, Category.comp_id, Category.id_comp])
  have hsk1 : sk ≫ ik = Spec.map rT ≫ s.1 := hk.lift_fst _ _ _
  have hsk2 : sk ≫ fk = 𝟙 _ := hk.lift_snd _ _ _
  let yZ : SquareZero.spec (ResidueField T') V ⟶ Z :=
    hZ.lift (SquareZero.toBase (ResidueField T') V ≫ sk) (𝟙 _)
      (by rw [Category.assoc, hsk2, Category.comp_id, Category.id_comp])
  have hyZ₁ : yZ ≫ q₁ = SquareZero.toBase (ResidueField T') V ≫ sk := hZ.lift_fst _ _ _
  have hyZ₂ : yZ ≫ q₂ = 𝟙 _ := hZ.lift_snd _ _ _

  have htoRed : (SmallExtension.toReduction T' T') =
      (algebraMap (ResidueField T') (ResidueField T' ⊗[T'] T')).comp (residue T') := by
    apply RingHom.ext
    intro t
    show (1 : ResidueField T') ⊗ₜ[T'] t = (residue T' t) ⊗ₜ[T'] (1 : T')
    calc (1 : ResidueField T') ⊗ₜ[T'] t = (1 : ResidueField T') ⊗ₜ[T'] (t • (1 : T')) := by rw [smul_eq_mul, mul_one]
      _ = t • ((1 : ResidueField T') ⊗ₜ[T'] (1 : T')) := TensorProduct.tmul_smul _ _ _
      _ = (t • (1 : ResidueField T')) ⊗ₜ[T'] (1 : T') := by rw [TensorProduct.smul_tmul']
      _ = (residue T' t) ⊗ₜ[T'] (1 : T') := by rw [Algebra.smul_def, mul_one, ResidueField.algebraMap_eq]
  let cY : Spec (CommRingCat.of (SmallExtension.thickening T' V T')) ⟶ Yk :=
    hk.lift (SmallExtension.thickeningFst T' V T' ≫ Spec.map (CommRingCat.ofHom (SmallExtension.toReduction T' T')) ≫ s.1)
      (SmallExtension.thickeningFst T' V T' ≫ SmallExtension.reductionBase T' T')
      (by
        rw [Category.assoc, Category.assoc, s.2, Category.comp_id, Category.assoc, htoRed, CommRingCat.ofHom_comp,
          Spec.map_comp])
  have hcY1 : cY ≫ ik = SmallExtension.thickeningFst T' V T' ≫
      Spec.map (CommRingCat.ofHom (SmallExtension.toReduction T' T')) ≫ s.1 := hk.lift_fst _ _ _
  have hcY2 : cY ≫ fk = SmallExtension.thickeningFst T' V T' ≫ SmallExtension.reductionBase T' T' := hk.lift_snd _ _ _
  let cZ : Spec (CommRingCat.of (SmallExtension.thickening T' V T')) ⟶ Z :=
    hZ.lift cY (SmallExtension.thickeningSnd T' V T')
      (by rw [hcY2]; exact (SmallExtension.thickening_isPullback (T' := T') V T').w)
  have hcZ1 : cZ ≫ q₁ = cY := hZ.lift_fst _ _ _
  have hcZ2 : cZ ≫ q₂ = SmallExtension.thickeningSnd T' V T' := hZ.lift_snd _ _ _

  have hsq : s.1 ≫ q = Spec.map (CommRingCat.ofHom (algebraMap T' T')) := by
    rw [s.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have haff : ∃ U : Y.Opens, IsAffineOpen U ∧ Set.range s.1.base ⊆ (U : Set Y) := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (s.1.base (closedPoint T'))) isOpen_univ
    refine ⟨U, hU, ?_⟩
    rintro _ ⟨p, rfl⟩
    have hp : p = closedPoint T' := by
      apply PrimeSpectrum.ext
      haveI := p.2
      exact (IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime p.1))
    rw [hp]; exact hxU
  have hchart := hΦchart f u.1 u.2 vv T' s.1 hsq haff cZ (by rw [← Category.assoc, hcZ1, hcY1]) hcZ2

  have hsu : (s.1 ≫ u.1) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap T' T')) := by
    rw [Category.assoc, u.2, hsq]
  have hvv1 : s.1 ≫ vv.1 = s.1 ≫ u.1 := hsec.symm
  rw [hvv1] at hchart
  have hcZw := K3Z.eq_const_of_isTangentOfPair_self I T' hI hsmall V ι hι hιI f (s.1 ≫ u.1) hsu _ hchart

  let fρ : ResidueField T' ⊗[T'] T' →ₐ[ResidueField T'] TrivSqZeroExt (ResidueField T') V :=
    (Algebra.ofId (ResidueField T') (TrivSqZeroExt (ResidueField T') V)).comp
      (Algebra.TensorProduct.rid T' (ResidueField T') (ResidueField T')).toAlgHom
  let ρ : SmallExtension.thickening T' V T' →+* TrivSqZeroExt (ResidueField T') V :=
    (Algebra.TensorProduct.lift fρ (AlgHom.id (ResidueField T') (TrivSqZeroExt (ResidueField T') V))
      (fun _ _ => Commute.all _ _)).toRingHom
  have hρ1 : ρ.comp (Algebra.TensorProduct.includeRight (R := ResidueField T') (A := ResidueField T' ⊗[T'] T')
      (B := TrivSqZeroExt (ResidueField T') V)).toRingHom = RingHom.id _ := by
    apply RingHom.ext; intro t
    show (Algebra.TensorProduct.lift fρ (AlgHom.id _ _) (fun _ _ => Commute.all _ _)) ((1 : ResidueField T' ⊗[T'] T') ⊗ₜ t) = t
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
  have hρ2 : ρ.comp ((Algebra.TensorProduct.includeLeftRingHom).comp (SmallExtension.toReduction T' T')) =
      (algebraMap (ResidueField T') (TrivSqZeroExt (ResidueField T') V)).comp (residue T') := by
    apply RingHom.ext; intro t
    show (Algebra.TensorProduct.lift fρ (AlgHom.id _ _) (fun _ _ => Commute.all _ _)) (((1 : ResidueField T') ⊗ₜ[T'] t) ⊗ₜ 1) =
      algebraMap (ResidueField T') (TrivSqZeroExt (ResidueField T') V) (residue T' t)
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    show algebraMap (ResidueField T') (TrivSqZeroExt (ResidueField T') V)
      (Algebra.TensorProduct.rid T' (ResidueField T') (ResidueField T') ((1 : ResidueField T') ⊗ₜ[T'] t)) = _
    rw [Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one, ResidueField.algebraMap_eq]
  have hρ3 : ρ.comp ((Algebra.TensorProduct.includeLeftRingHom).comp
      (algebraMap (ResidueField T') (ResidueField T' ⊗[T'] T'))) =
      algebraMap (ResidueField T') (TrivSqZeroExt (ResidueField T') V) := by
    apply RingHom.ext; intro a
    show (Algebra.TensorProduct.lift fρ (AlgHom.id _ _) (fun _ _ => Commute.all _ _)) ((a ⊗ₜ[T'] (1 : T')) ⊗ₜ 1) =
      algebraMap (ResidueField T') (TrivSqZeroExt (ResidueField T') V) a
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    show algebraMap (ResidueField T') (TrivSqZeroExt (ResidueField T') V)
      (Algebra.TensorProduct.rid T' (ResidueField T') (ResidueField T') (a ⊗ₜ[T'] (1 : T'))) = _
    rw [Algebra.TensorProduct.rid_tmul, one_smul]
  let ε : SquareZero.spec (ResidueField T') V ⟶ Spec (CommRingCat.of (SmallExtension.thickening T' V T')) :=
    Spec.map (CommRingCat.ofHom ρ)
  have hε2 : ε ≫ SmallExtension.thickeningSnd T' V T' = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ1, CommRingCat.ofHom_id, Spec.map_id]
  have hε1 : ε ≫ SmallExtension.thickeningFst T' V T' ≫ Spec.map (CommRingCat.ofHom (SmallExtension.toReduction T' T')) =
      SquareZero.toBase (ResidueField T') V ≫ Spec.map rT := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hρ2,
      CommRingCat.ofHom_comp, Spec.map_comp]
    rfl
  have hε3 : ε ≫ SmallExtension.thickeningFst T' V T' ≫ SmallExtension.reductionBase T' T' =
      SquareZero.toBase (ResidueField T') V := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hρ3]
    rfl
  rw [← hwdef] at hcZw
  have hcomp : Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeLeftRingHom).comp
      (SmallExtension.toReduction T' T'))) =
      SmallExtension.thickeningFst T' V T' ≫ Spec.map (CommRingCat.ofHom (SmallExtension.toReduction T' T')) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hε1' : ∀ {W : Scheme.{u}} (h : Spec (CommRingCat.of T') ⟶ W),
      ε ≫ SmallExtension.thickeningFst T' V T' ≫ Spec.map (CommRingCat.ofHom (SmallExtension.toReduction T' T')) ≫ h =
        SquareZero.toBase (ResidueField T') V ≫ Spec.map rT ≫ h := by
    intro W h
    simpa only [Category.assoc] using congrArg (· ≫ h) hε1
  have hsk1' : ∀ {W : Scheme.{u}} (h : Y ⟶ W), sk ≫ ik ≫ h = Spec.map rT ≫ s.1 ≫ h := by
    intro W h
    rw [← Category.assoc, hsk1, Category.assoc]

  have hεcZ : ε ≫ cZ = yZ := by
    apply hZ.hom_ext
    · rw [Category.assoc, hcZ1, hyZ₁]
      apply hk.hom_ext
      · simp only [Category.assoc, hcY1, hsk1]
        exact hε1' _
      · simp only [Category.assoc, hcY2, hsk2, Category.comp_id]
        exact hε3
    · rw [Category.assoc, hcZ2, hyZ₂, hε2]

  have hconst : yZ ≫ w₀ = SquareZero.toBase (ResidueField T') V ≫ sk ≫ SquareZero.zeroSection V fk q₁ q₂ hZ ≫ w₀ := by
    rw [← cancel_mono jA]
    simp only [Category.assoc]
    rw [hjw]
    calc yZ ≫ w = ε ≫ cZ ≫ w := by rw [← hεcZ, Category.assoc]
      _ = ε ≫ SmallExtension.thickeningFst T' V T' ≫
            Spec.map (CommRingCat.ofHom (SmallExtension.toReduction T' T')) ≫ s.1 ≫ u.1 := by
          rw [hcZw, hcomp]; simp only [Category.assoc]
      _ = SquareZero.toBase (ResidueField T') V ≫ Spec.map rT ≫ s.1 ≫ u.1 := hε1' _
      _ = SquareZero.toBase (ResidueField T') V ≫ sk ≫ ik ≫ u.1 := by rw [hsk1']
      _ = SquareZero.toBase (ResidueField T') V ≫ sk ≫ SquareZero.zeroSection V fk q₁ q₂ hZ ≫ w := by rw [hw0]

  have hH0 := K3Inf.bijective_appTop_specialFibre q hconn ik fk hk
  haveI : IsProper fk := MorphismProperty.of_isPullback (P := @IsProper) hk inferInstance
  haveI : CompactSpace ↥Yk := inferInstance
  haveI : QuasiSeparatedSpace ↥Yk := quasiSeparatedSpace_of_quasiSeparated fk
  have hB := AlgebraicGeometry.RelTangentPoints.eq_comp_zeroSection_of_thickenedPoint_comp_eq xk Lk V fk hH0 q₁ q₂ hZ
    w₀ hw₀x sk yZ hyZ₁ hyZ₂ hconst

  have := congrArg (· ≫ jA) hB
  simp only [Category.assoc] at this
  rw [hjw, hw0] at this
  exact this

theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (hc₀ : L₀.IsCommutative)
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    {Y Y₀ : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T')) (hq : Smooth q) (hqp : IsProper q)
    (hconn : ∀ x : Spec (CommRingCat.of T'), _root_.IsConnected (q.base ⁻¹' {x}))
    (q₀ : Y₀ ⟶ Spec (CommRingCat.of T)) (gY : Y₀ ⟶ Y) (hgY : IsPullback gY q₀ q (Spec.map (CommRingCat.ofHom π)))
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of T'))) q)
    (u v : SchemeHomOver q f) (hred : gY ≫ u.1 = gY ≫ v.1) (hsec : s.1 ≫ u.1 = s.1 ≫ v.1) :
    u = v := by
  classical
  haveI := hq
  haveI := hqp

  have hItop : RingHom.ker π ≠ ⊤ := by
    intro h
    obtain ⟨n, hn⟩ := hker
    rw [h, Ideal.top_pow] at hn
    have : (1 : T') ∈ (⊥ : Ideal T') := by rw [← Ideal.zero_eq_bot, ← hn]; trivial
    exact one_ne_zero ((Ideal.mem_bot).mp this)
  have hI : RingHom.ker π ≤ maximalIdeal T' := IsLocalRing.le_maximalIdeal hItop

  have htors : Module.IsTorsionBySet T' ↥(RingHom.ker π) (maximalIdeal T' : Set T') := by
    rintro x ⟨a, ha⟩
    apply Subtype.ext
    show a • (x : T') = 0
    have : (x : T') * a ∈ RingHom.ker π * maximalIdeal T' := Ideal.mul_mem_mul x.2 ha
    rw [hsmall, Ideal.mem_bot] at this
    rw [smul_eq_mul, mul_comm]
    exact this
  letI instk : Module (ResidueField T') ↥(RingHom.ker π) := htors.module
  letI instkop : Module (ResidueField T')ᵐᵒᵖ ↥(RingHom.ker π) :=
    Module.compHom _ (RingHom.fromOpposite (RingHom.id (ResidueField T')) fun a b => Commute.all a b)
  haveI : IsCentralScalar (ResidueField T') ↥(RingHom.ker π) := ⟨fun _ _ => rfl⟩
  haveI : IsScalarTower T' (ResidueField T') ↥(RingHom.ker π) := htors.isScalarTower
  haveI : Module.Finite T' ↥(RingHom.ker π) := inferInstance
  haveI : Module.Finite (ResidueField T') ↥(RingHom.ker π) :=
    Module.Finite.of_restrictScalars_finite T' (ResidueField T') _
  exact K3_core π hπ (RingHom.ker π) rfl hI hsmall ↥(RingHom.ker π) (RingHom.ker π).subtype
    (Submodule.injective_subtype _) (by rw [Submodule.range_subtype, Submodule.restrictScalars_self])
    f f₀ g hg L₀ q hconn gY q₀ hgY s u v hred hsec

end S_GoodReductionJacobian_RelativeGroupLaw_eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot (solution)
