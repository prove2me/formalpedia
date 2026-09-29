-- Prove2me | solution 1 for NeronModelInfra.exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7bb46851-f122-5e89-8a41-2556cc2fcc3e

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_NeronModelInfra_TopFormOrder
import Definitions.Def_NeronModelInfra_OmegaMinimalComponentData

import Theorems.Thm_NeronModelInfra_ComponentReading_exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes
import Theorems.Thm_NeronModelInfra_TopFormOrder_eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le
import Theorems.Thm_AlgebraicGeometry_bijective_kaehlerDifferential_map_comp_mapBaseChange_stalk_pullback
import Theorems.Thm_NeronModelInfra_isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift
import Theorems.Thm_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes
import Theorems.Thm_Algebra_FormallyEtale_of_formallySmooth_of_bijective_mapBaseChange
import Theorems.Thm_NeronModelInfra_mul_pointGenericFibre_eq_pointGenericFibre_comp_chart_of_genericFibreRestrict_comp_eq_mul
import Theorems.Thm_NeronModelInfra_MinimalComponentData_exists_ringHom_stalk_chart_comp_eq_pointGenericFibre_of_forall_specializes
import Theorems.Thm_NeronModelInfra_TopFormOrder_topFormMap_topFormMap
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_topToSections_bijective_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk
import Theorems.Thm_KaehlerDifferential_bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
p2m_attr_erase "instance" "NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

namespace G2Glue

theorem pointGenericFibre_comp_genericFibreRestrict
    {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
    {X U : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (u : U ⟶ Spec (CommRingCat.of R))
    (q : U ⟶ X) (hq : q ≫ f = u) (η : U) (x : X)
    [Algebra R (U.presheaf.stalk η)]
    (halgU : U.fromSpecStalk η ≫ u = Spec.map (CommRingCat.ofHom (algebraMap R (U.presheaf.stalk η))))
    [Algebra R (X.presheaf.stalk x)]
    (halgX : X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk x))))
    (F : Type u) [CommRing F] [Algebra (U.presheaf.stalk η) F] [Algebra (X.presheaf.stalk x) F]
    [Algebra R F] [Algebra K F] [IsScalarTower R (U.presheaf.stalk η) F]
    [IsScalarTower R (X.presheaf.stalk x) F] [IsScalarTower R K F]
    (hF : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) F)) ≫ X.fromSpecStalk x =
      Spec.map (CommRingCat.ofHom (algebraMap (U.presheaf.stalk η) F)) ≫ U.fromSpecStalk η ≫ q) :
    (pointGenericFibre (K := K) (K' := F)
        (⟨U.fromSpecStalk η, halgU⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (U.presheaf.stalk η)))) u)).1 ≫
      (genericFibreRestrict R K f u ⟨q, hq⟩).1 =
    (pointGenericFibre (K := K) (K' := F)
        (⟨X.fromSpecStalk x, halgX⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk x)))) f)).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, pointGenericFibre_coe_comp_fst, hF]
    simp only [genericFibreRestrict, pullback.lift_fst]
    rw [← Category.assoc, pointGenericFibre_coe_comp_fst, Category.assoc]
  · rw [Category.assoc, pointGenericFibre_coe_comp_snd]
    simp only [genericFibreRestrict, pullback.lift_snd]
    rw [pointGenericFibre_coe_comp_snd]

end G2Glue

namespace T3Glue

theorem exists_affine_chart_of_point
    {K : Type u} [Field K] {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (ω : Γ(gK.topDifferentials d, ⊤))
    (F : Type u) [Field F] [Algebra K F] (φ : Spec (CommRingCat.of F) ⟶ XK)
    (hφ : φ ≫ gK = Spec.map (CommRingCat.ofHom (algebraMap K F))) :
    ∃ (U'' : XK.Opens) (hU'' : IsAffineOpen U'') (algU'' : Algebra Γ(XK, U'') F)
      (_ : letI := gK.sectionsAlgebra U''; IsScalarTower K Γ(XK, U'') F)
      (_ : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U'') F)) ≫ hU''.fromSpec = φ)
      (ωU'' : ⋀[Γ(XK, U'')]^d (gK.kaehlerPresheaf.obj (op U''))),
      gK.topToSections d U'' ωU'' = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω := by
  classical

  let pt : ↥(Spec (CommRingCat.of F)) := (default : PrimeSpectrum F)
  have hpt : ∀ q : ↥(Spec (CommRingCat.of F)), q = pt := fun q => Subsingleton.elim (α := PrimeSpectrum F) q pt
  obtain ⟨_, ⟨(U'' : XK.Opens), (hU'' : IsAffineOpen U''), rfl⟩, hxU, -⟩ :=
    XK.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (φ.base pt)) isOpen_univ

  have hrange : Set.range φ.base ⊆ Set.range U''.ι.base := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι, hpt q]
    exact hxU
  have hl : IsOpenImmersion.lift U''.ι φ hrange ≫ U''.ι = φ := IsOpenImmersion.lift_fac _ _ _
  let ρ : Γ(XK, U'') ⟶ CommRingCat.of F := Spec.preimage (IsOpenImmersion.lift U''.ι φ hrange ≫ hU''.isoSpec.hom)
  have hρ : Spec.map ρ ≫ hU''.fromSpec = φ := by
    rw [Spec.map_preimage, Category.assoc, ← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc, hl]
  letI algU'' : Algebra Γ(XK, U'') F := ρ.hom.toAlgebra
  letI := gK.sectionsAlgebra U''

  have hK : CommRingCat.ofHom (algebraMap K F) =
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ gK.appLE ⊤ U'' le_top) ≫ ρ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
      IsAffineOpen.SpecMap_appLE_fromSpec gK (isAffineOpen_top _) hU'' le_top, reassoc_of% hρ, hφ]
  have htower : IsScalarTower K Γ(XK, U'') F :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hK)
  obtain ⟨ωU'', hω⟩ := (AlgebraicGeometry.Scheme.Hom.topToSections_bijective_of_isAffineOpen gK d hU'').2
    ((gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω)
  exact ⟨U'', hU'', algU'', htower, hρ, ωU'', hω⟩

end T3Glue

namespace T3Glue

theorem bijective_map_comp_mapBaseChange_stalk_of_isOpenImmersion
    {R : Type u} [CommRing R] {X Z U : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : Z ⟶ Spec (CommRingCat.of R))
    (ι : U ⟶ pullback z f) [IsOpenImmersion ι] (u : ↥U)
    (g : U ⟶ Z) (hg : g = ι ≫ pullback.fst z f) (ζ : ↥Z) (hζ : g.base u = ζ)
    [Algebra R (Z.presheaf.stalk ζ)]
    (halgZ : Z.fromSpecStalk ζ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ζ))))
    [Algebra R (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))]
    (halgX : X.fromSpecStalk ((pullback.snd z f).base (ι.base u)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base (ι.base u))))))
    (O₀ : Type u) [CommRing O₀] [Algebra R O₀] (φ : O₀ →+* (X.presheaf.stalk ((pullback.snd z f).base (ι.base u))))
    (hφ : Function.Bijective φ) (hφR : φ.comp (algebraMap R O₀) = algebraMap R (X.presheaf.stalk ((pullback.snd z f).base (ι.base u))))
    [Algebra R (U.presheaf.stalk u)] [Algebra (Z.presheaf.stalk ζ) (U.presheaf.stalk u)] [Algebra O₀ (U.presheaf.stalk u)]
    (hA : ∀ a, algebraMap (Z.presheaf.stalk ζ) (U.presheaf.stalk u) a =
      (g.stalkMap u).hom ((Z.presheaf.stalkCongr (.of_eq hζ.symm)).hom a))
    (hB : ∀ b, algebraMap O₀ (U.presheaf.stalk u) b = ((ι ≫ pullback.snd z f).stalkMap u).hom (φ b))
    [IsScalarTower R (Z.presheaf.stalk ζ) (U.presheaf.stalk u)] [IsScalarTower R O₀ (U.presheaf.stalk u)] :
    Function.Bijective
      ((KaehlerDifferential.map R (Z.presheaf.stalk ζ) (U.presheaf.stalk u) (U.presheaf.stalk u)).restrictScalars (U.presheaf.stalk u) ∘ₗ
        KaehlerDifferential.mapBaseChange R O₀ (U.presheaf.stalk u)) := by
  subst hζ
  subst hg
  have hpt : (ι ≫ pullback.fst z f).base u = (pullback.fst z f).base (ι.base u) := rfl

  have hA' : ∀ a, algebraMap (Z.presheaf.stalk ((ι ≫ pullback.fst z f).base u)) (U.presheaf.stalk u) a =
      (ι.stalkMap u).hom (((pullback.fst z f).stalkMap (ι.base u)).hom a) := by
    intro a
    rw [hA, Scheme.Hom.stalkMap_comp]
    simp [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  have hB' : ∀ b, algebraMap O₀ (U.presheaf.stalk u) b =
      (ι.stalkMap u).hom (((pullback.snd z f).stalkMap (ι.base u)).hom (φ b)) := by
    intro b
    rw [hB, Scheme.Hom.stalkMap_comp]
    rfl

  letI instZ : Algebra R (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) := ‹Algebra R (Z.presheaf.stalk ((ι ≫ pullback.fst z f).base u))›
  letI instZO : Algebra (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) (U.presheaf.stalk u) := ‹Algebra (Z.presheaf.stalk ((ι ≫ pullback.fst z f).base u)) (U.presheaf.stalk u)›
  haveI : IsScalarTower R (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) (U.presheaf.stalk u) := ‹IsScalarTower R (Z.presheaf.stalk ((ι ≫ pullback.fst z f).base u)) (U.presheaf.stalk u)›
  obtain ⟨𝔔, h𝔔, e, he₁, he₂⟩ := AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk f z (ι.base u) halgZ halgX
  haveI : 𝔔.IsPrime := h𝔔

  let ιu : ((pullback z f).presheaf.stalk (ι.base u)) ≃+* (U.presheaf.stalk u) := (asIso (ι.stalkMap u)).commRingCatIsoToRingEquiv
  have hιu : ∀ s, ιu s = (ι.stalkMap u).hom s := fun _ => rfl
  let eO : (U.presheaf.stalk u) ≃+* Localization.AtPrime 𝔔 := ιu.symm.trans e
  letI algT : Algebra ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) (U.presheaf.stalk u) :=
    (eO.symm.toRingHom.comp (algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) (Localization.AtPrime 𝔔))).toAlgebra
  have halgT : ∀ t, algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) (U.presheaf.stalk u) t = ιu (e.symm (algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) (Localization.AtPrime 𝔔) t)) :=
    fun _ => rfl
  let eT : Localization.AtPrime 𝔔 ≃ₐ[((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u))))] (U.presheaf.stalk u) := AlgEquiv.ofRingEquiv (f := eO.symm) (fun _ => rfl)
  haveI hlocT : IsLocalization 𝔔.primeCompl (U.presheaf.stalk u) := IsLocalization.isLocalization_of_algEquiv 𝔔.primeCompl eT

  let φₐ : O₀ ≃ₐ[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u))) :=
    AlgEquiv.ofBijective { toRingHom := φ, commutes' := fun r => RingHom.congr_fun hφR r } hφ
  have hφₐ : ∀ b, φₐ b = φ b := fun _ => rfl
  let Ψ : ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀) ≃ₐ[R] ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) := Algebra.TensorProduct.congr AlgEquiv.refl φₐ
  have hΨ : ∀ (a : (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u)))) (b : O₀), Ψ (a ⊗ₜ[R] b) = a ⊗ₜ[R] φ b := fun a b => by
    show Algebra.TensorProduct.map (AlgEquiv.refl : (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ≃ₐ[R] (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u)))).toAlgHom φₐ.toAlgHom (a ⊗ₜ[R] b) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  letI algT₀ : Algebra ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀) (U.presheaf.stalk u) :=
    ((algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) (U.presheaf.stalk u)).comp (Ψ.symm.toRingEquiv).symm.toRingHom).toAlgebra
  haveI hloc₀ : IsLocalization (𝔔.primeCompl.map (Ψ.symm.toRingEquiv : ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) ≃* ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀))) (U.presheaf.stalk u) :=
    IsLocalization.isLocalization_of_base_ringEquiv 𝔔.primeCompl (U.presheaf.stalk u) Ψ.symm.toRingEquiv
  have halgT₀ : ∀ t, algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀) (U.presheaf.stalk u) t = algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) (U.presheaf.stalk u) (Ψ t) := by
    intro t
    show algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) (U.presheaf.stalk u) ((Ψ.symm.toRingEquiv).symm t) = _
    simp

  haveI : IsScalarTower (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀) (U.presheaf.stalk u) :=
    IsScalarTower.of_algebraMap_eq (R := (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u)))) (S := ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀)) (A := (U.presheaf.stalk u)) fun a => by
      rw [halgT₀, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hΨ, map_one,
        halgT, ← he₁, RingEquiv.symm_apply_apply, hιu]
      exact hA' a
  have hBT : (algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀) (U.presheaf.stalk u)).comp
      (Algebra.TensorProduct.includeRight (R := R) (A := (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u)))) (B := O₀)).toRingHom =
      algebraMap O₀ (U.presheaf.stalk u) := by
    refine RingHom.ext fun b => ?_
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply,
      halgT₀, hΨ, halgT, ← he₂, RingEquiv.symm_apply_apply, hιu, hB']
  haveI : IsLocalization (⊥ : Submonoid (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u)))) (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) := IsLocalization.self (by simp)
  exact KaehlerDifferential.bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct R (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) O₀ (U.presheaf.stalk u)
    (⊥ : Submonoid (Z.presheaf.stalk ((pullback.fst z f).base (ι.base u)))) hBT (𝔔.primeCompl.map (Ψ.symm.toRingEquiv : ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base (ι.base u)))) ≃* ((Z.presheaf.stalk ((pullback.fst z f).base (ι.base u))) ⊗[R] O₀)))

end T3Glue

theorem tfm_KK (K K' B F : Type u) [Field K] [Field K'] [Algebra K K'] [CommRing B] [Algebra K B] [Field F]
    [Algebra B F] [Algebra K F] [Algebra K' F] [IsScalarTower K B F] [IsScalarTower K K' F]
    (d : ℕ) (ω : ⋀[B]^d (Ω[B⁄K])) :
    TopFormOrder.topFormMap K K' F F d (TopFormOrder.topFormMap K K B F d ω) = TopFormOrder.topFormMap K K' B F d ω := by
  rw [NeronModelInfra.TopFormOrder.topFormMap_topFormMap K K K' B F F d ω]

theorem tfm_KE (K K' B E F : Type u) [Field K] [Field K'] [Algebra K K'] [CommRing B] [Algebra K B] [Field E] [Field F]
    [Algebra B E] [Algebra E F] [Algebra B F] [IsScalarTower B E F]
    [Algebra K E] [IsScalarTower K B E] [Algebra K F] [Algebra K' F] [IsScalarTower K E F] [IsScalarTower K K' F]
    [IsScalarTower K B F]
    (d : ℕ) (ω : ⋀[B]^d (Ω[B⁄K])) :
    TopFormOrder.topFormMap K K' E F d (TopFormOrder.topFormMap K K B E d ω) = TopFormOrder.topFormMap K K' B F d ω := by
  rw [NeronModelInfra.TopFormOrder.topFormMap_topFormMap K K K' B E F d ω]

theorem stalkAlgebraMap_comp' {R : Type u} [CommRing R] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (f : Y ⟶ Spec (CommRingCat.of R)) (x : X) :
    (g.stalkMap x).hom.comp (stalkAlgebraMap f (g.base x)) = stalkAlgebraMap (g ≫ f) x := by
  ext r
  simp only [RingHom.comp_apply, stalkAlgebraMap_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  erw [Scheme.Hom.germ_stalkMap_apply]
  rfl

namespace C7Glue

theorem injective_of_map_irreducible_ne_zero {A B : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] (f : A →+* B) (ϖ : A) (hϖ : Irreducible ϖ) (h : f ϖ ≠ 0) :
    Function.Injective f := by
  refine (injective_iff_map_eq_zero f).mpr (fun a ha => ?_)
  by_contra ha0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  rw [map_mul, map_pow] at ha
  exact pow_ne_zero n h ((IsUnit.map f u.isUnit).mul_right_eq_zero.mp ha)

theorem map_uniformizer_ne_zero {A B : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] (f : A →+* B) (ϖ : A)
    (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (h : Ideal.map f (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B) : f ϖ ≠ 0 := by
  intro h0
  rw [hϖ, Ideal.map_span, Set.image_singleton, h0, Ideal.span_singleton_eq_bot.mpr rfl] at h
  exact IsDiscreteValuationRing.not_a_field B h.symm

theorem maximalIdeal_eq_span_map {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (f : A →+* B) (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (h : Ideal.map f (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B) :
    IsLocalRing.maximalIdeal B = Ideal.span {f ϖ} := by
  rw [← h, hϖ, Ideal.map_span, Set.image_singleton]

end C7Glue

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1280000 in
theorem solution    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤)) (hωframe : Scheme.Modules.IsFrameOn ω ⊤)
    (hleft : (∀ (L F : Type u) [Field L] [Field F] [Algebra K L] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
        (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) gK)
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) gK)
        (U' U'' : XK.Opens) (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'')
        [Algebra Γ(XK, U') F] [Algebra Γ(XK, U'') F],
        letI := gK.sectionsAlgebra U'; letI := gK.sectionsAlgebra U''
        ∀ [IsScalarTower K Γ(XK, U') F] [IsScalarTower K Γ(XK, U'') F],
        Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U') F)) ≫ hU'.fromSpec = x.1 →
        Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U'') F)) ≫ hU''.fromSpec =
          (LXK.mul (Spec.map (CommRingCat.ofHom (algebraMap K F)))
            ⟨Spec.map (CommRingCat.ofHom (algebraMap L F)) ≫ a.1, by
              rw [Category.assoc, a.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                ← IsScalarTower.algebraMap_eq]⟩ x).1 →
        ∀ (ω' : ⋀[Γ(XK, U')]^d (gK.kaehlerPresheaf.obj (op U')))
          (ω'' : ⋀[Γ(XK, U'')]^d (gK.kaehlerPresheaf.obj (op U''))),
          gK.topToSections d U' ω' = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          gK.topToSections d U'' ω'' = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          TopFormOrder.topFormMap K L Γ(XK, U'') F d ω'' = TopFormOrder.topFormMap K L Γ(XK, U') F d ω'))
    (D : MinimalComponentData R K gK d ω) (hD : D.IsOmegaMinimal)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    (V : ∀ c : D.ι, ((D.C c).Y).Opens) (j : ∀ c : D.ι, SchemeHomOver ((V c).ι ≫ (D.C c).f) f)
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [IsIso e.1]
    (hyV : ∀ c, (D.C c).y ∈ V c)
    (hVK : ∀ c (y' : ↥(D.C c).Y), (D.C c).f.base y' ≠ IsLocalRing.closedPoint R → y' ∈ V c)
    (hjopen : ∀ c, IsOpenImmersion (j c).1)
    (hjchart : ∀ c, (genericFibreRestrict R K f ((V c).ι ≫ (D.C c).f) (j c)).1 ≫ e.1 =
      (genericFibreRestrict R K (D.C c).f ((V c).ι ≫ (D.C c).f) ⟨(V c).ι, rfl⟩).1 ≫ (D.C c).e.1)
    (hcover : ∀ x : ↥X, ∃ c, x ∈ Set.range (j c).1.base)
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (η : ↑(pullback z f)) (hη : (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R)
    (hmax : ∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η)
    (T : ComponentReading R K gK d ω)
    (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀) (τ₀ : SchemeHomOver (U₀.ι ≫ pullback.fst z f ≫ z) T.f)
    (hτ₀ : (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K T.f (U₀.ι ≫ pullback.fst z f ≫ z) τ₀) T.e).1 =
            pullback.map (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U₀.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f) (hv₁ : v ≫ pullback.fst z T.f = U₀.ι ≫ pullback.fst z f)
    (hv₂ : v ≫ pullback.snd z T.f = τ₀.1)
    (hgen : T.y ⤳ τ₀.1.base ⟨η, hηU⟩) :
    (∃ c : D.ι, T.n = (D.C c).n) ∧
      letI : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := (v.stalkMap ⟨η, hηU⟩).hom.toAlgebra
      Algebra.FormallySmooth ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := by
  classical

  haveI : Smooth (pullback.fst z f) := inferInstance
  let ηU : ↥U₀ := ⟨η, hηU⟩
  let η' : ↥(pullback z T.f) := v.base ηU
  let ζ₀ : ↥Z := (pullback.fst z T.f).base η'
  have hζ₀ : (U₀.ι ≫ pullback.fst z f).base ηU = ζ₀ := by
    show (U₀.ι ≫ pullback.fst z f).base ηU = (v ≫ pullback.fst z T.f).base ηU
    rw [hv₁]
  letI algR'O' : Algebra (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') :=
    ((pullback.fst z T.f).stalkMap η').hom.toAlgebra
  letI algO'O : Algebra ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) :=
    (v.stalkMap ηU).hom.toAlgebra
  letI algR'O : Algebra (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) :=
    ((v.stalkMap ηU).hom.comp ((pullback.fst z T.f).stalkMap η').hom).toAlgebra
  haveI : IsScalarTower (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η')
      ((U₀ : Scheme.{u}).presheaf.stalk ηU) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have hFS : Algebra.FormallySmooth (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := by
    haveI : Smooth (v ≫ pullback.fst z T.f) := by rw [hv₁]; infer_instance
    have hmem : ηU ∈ (v ≫ pullback.fst z T.f).smoothLocus := by
      rw [Scheme.Hom.smoothLocus_eq_top]; trivial
    have hfs : ((v ≫ pullback.fst z T.f).stalkMap ηU).hom.FormallySmooth := (Scheme.Hom.mem_smoothLocus).mp hmem
    rw [Scheme.Hom.stalkMap_comp] at hfs
    exact hfs

  have hmain : (∃ c : D.ι, T.n = (D.C c).n) ∧
      Function.Bijective (KaehlerDifferential.mapBaseChange (Z.presheaf.stalk ζ₀)
        ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := by

    let y₁ : ↥T.Y := (pullback.snd z T.f).base η'
    have hy₁ : τ₀.1.base ηU = y₁ := by
      show τ₀.1.base ηU = (v ≫ pullback.snd z T.f).base ηU
      rw [hv₂]
    have hgen₁ : T.y ⤳ y₁ := hy₁ ▸ hgen
    have hmaxU : ∀ y : ↥U₀, y ⤳ ηU → (U₀.ι ≫ pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = ηU := by
      intro y hy hsp
      apply Subtype.ext
      exact hmax (U₀.ι.base y) (hy.map U₀.ι.base.hom.continuous) hsp
    have e₁ : v ≫ pullback.snd z T.f ≫ T.f = U₀.ι ≫ pullback.fst z f ≫ z := by
      rw [← pullback.condition, ← Category.assoc, hv₁, Category.assoc]
    have e₂ : (U₀.ι ≫ pullback.snd z f) ≫ f = U₀.ι ≫ pullback.fst z f ≫ z := by
      rw [Category.assoc, ← pullback.condition]
    have e₃ : (v ≫ pullback.fst z T.f) ≫ z = U₀.ι ≫ pullback.fst z f ≫ z := by
      rw [hv₁, Category.assoc]
    have hηsp : (U₀.ι ≫ pullback.fst z f ≫ z).base ηU = IsLocalRing.closedPoint R := hη
    have hy₁sp : T.f.base y₁ = IsLocalRing.closedPoint R := by
      have h := congrArg (fun φ => φ.base ηU) e₁
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
      rw [← hηsp]; exact h
    have hξsp : f.base ((pullback.snd z f).base (U₀.ι.base ηU)) = IsLocalRing.closedPoint R := by
      have h := congrArg (fun φ => φ.base ηU) e₂
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
      rw [← hηsp]; exact h
    have hζ₀sp : z.base ζ₀ = IsLocalRing.closedPoint R := by
      have h := congrArg (fun φ => φ.base ηU) e₃
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
      rw [← hηsp]; exact h
    have hξmax : ∀ y : ↥X, y ⤳ ((pullback.snd z f).base (U₀.ι.base ηU)) → f.base y = IsLocalRing.closedPoint R → y = ((pullback.snd z f).base (U₀.ι.base ηU)) := by
      intro y hy hysp
      have hy2 : y ⤳ (U₀.ι ≫ pullback.snd z f).base ηU := hy
      obtain ⟨y', hy', rfl⟩ := Flat.generalizingMap (U₀.ι ≫ pullback.snd z f) hy2
      have hsp' : (U₀.ι ≫ pullback.fst z f ≫ z).base y' = IsLocalRing.closedPoint R := by
        rw [← e₂, Scheme.Hom.comp_apply]; exact hysp
      rw [hmaxU y' hy' hsp']
      rfl
    have hζ₀max : ∀ y : ↥Z, y ⤳ ζ₀ → z.base y = IsLocalRing.closedPoint R → y = ζ₀ := by
      intro y hy hysp
      have hy2 : y ⤳ (U₀.ι ≫ pullback.fst z f).base ηU := by rw [hζ₀]; exact hy
      obtain ⟨y', hy', rfl⟩ := Flat.generalizingMap (U₀.ι ≫ pullback.fst z f) hy2
      have hsp' : (U₀.ι ≫ pullback.fst z f ≫ z).base y' = IsLocalRing.closedPoint R := by
        rw [← Category.assoc, Scheme.Hom.comp_apply]; exact hysp
      rw [hmaxU y' hy' hsp']
      exact hζ₀

    letI algRR' : Algebra R (Z.presheaf.stalk ζ₀) := stalkAlgebra z ζ₀
    have halgZ : Z.fromSpecStalk ζ₀ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ζ₀))) :=
      fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra z ζ₀
    letI algRO' : Algebra R ((pullback z T.f).presheaf.stalk η') := ((algebraMap (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η')).comp (algebraMap R (Z.presheaf.stalk ζ₀))).toAlgebra
    letI algRO : Algebra R ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp (algebraMap R (Z.presheaf.stalk ζ₀))).toAlgebra
    haveI : IsScalarTower R (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : IsScalarTower R (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : IsScalarTower R ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have halgO : (U₀ : Scheme.{u}).fromSpecStalk ηU ≫ (U₀.ι ≫ pullback.fst z f ≫ z) =
        Spec.map (CommRingCat.ofHom (algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ηU))) := by
      have hmap : algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ηU) = stalkAlgebraMap (U₀.ι ≫ pullback.fst z f ≫ z) ηU := by
        show ((v.stalkMap ηU).hom.comp ((pullback.fst z T.f).stalkMap η').hom).comp (stalkAlgebraMap z ζ₀) = _
        rw [RingHom.comp_assoc, stalkAlgebraMap_comp', stalkAlgebraMap_comp', ← Category.assoc, hv₁, Category.assoc]
      rw [hmap]
      exact fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra (U₀.ι ≫ pullback.fst z f ≫ z) ηU
    letI algRO₁ : Algebra R (T.Y.presheaf.stalk y₁) := stalkAlgebra T.f y₁
    have halg₁ : T.Y.fromSpecStalk y₁ ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁))) :=
      fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra T.f y₁
    letI algO₁O' : Algebra (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η') := ((pullback.snd z T.f).stalkMap η').hom.toAlgebra
    haveI : IsScalarTower R (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η') := IsScalarTower.of_algebraMap_eq (fun r => by
      show ((pullback.fst z T.f).stalkMap η').hom (stalkAlgebraMap z ζ₀ r) =
        ((pullback.snd z T.f).stalkMap η').hom (stalkAlgebraMap T.f y₁ r)
      rw [← RingHom.comp_apply, ← RingHom.comp_apply, stalkAlgebraMap_comp', stalkAlgebraMap_comp', pullback.condition])
    letI algO₁O : Algebra (T.Y.presheaf.stalk y₁) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp (algebraMap (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η'))).toAlgebra
    haveI : IsScalarTower (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : IsScalarTower R (T.Y.presheaf.stalk y₁) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := IsScalarTower.of_algebraMap_eq (fun x => by
      show _ = algebraMap ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) (algebraMap (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η') (algebraMap R (T.Y.presheaf.stalk y₁) x))
      rw [← IsScalarTower.algebraMap_apply R (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η'), ← IsScalarTower.algebraMap_apply R ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU)])

    letI algRX : Algebra R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) := stalkAlgebra f ((pullback.snd z f).base (U₀.ι.base ηU))
    have halgX : X.fromSpecStalk ((pullback.snd z f).base (U₀.ι.base ηU)) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))))) :=
      fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra f ((pullback.snd z f).base (U₀.ι.base ηU))
    letI algXO : Algebra (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom.toAlgebra
    have hpin1 : ((v.stalkMap ηU).hom.comp ((pullback.fst z T.f).stalkMap η').hom).comp (stalkAlgebraMap z ζ₀) =
        stalkAlgebraMap (U₀.ι ≫ pullback.fst z f ≫ z) ηU := by
      rw [RingHom.comp_assoc, stalkAlgebraMap_comp', stalkAlgebraMap_comp', ← Category.assoc, hv₁, Category.assoc]
    have hpin2 : ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom.comp (stalkAlgebraMap f ((pullback.snd z f).base (U₀.ι.base ηU))) =
        stalkAlgebraMap (U₀.ι ≫ pullback.fst z f ≫ z) ηU := by
      have h := stalkAlgebraMap_comp' (U₀.ι ≫ pullback.snd z f) f ηU
      rw [Category.assoc, ← pullback.condition] at h
      exact h
    haveI : IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := IsScalarTower.of_algebraMap_eq (fun r =>
      (RingHom.congr_fun hpin1 r).trans (RingHom.congr_fun hpin2 r).symm)

    obtain ⟨hdomO, hdomO', hfrac⟩ :=
      NeronModelInfra.isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift
        K LXK d ω X f e Z z uK η T U₀ hηU τ₀ hτ₀ v hv₁ hv₂
    haveI := hdomO; haveI := hdomO'
    obtain ⟨hdomO2, hdvrO, hlocO, hidxO⟩ :=
      NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes (U₀.ι ≫ pullback.fst z f ≫ z) ηU
        (by simpa using hη) hmaxU halgO
    haveI := hdvrO; haveI := hlocO
    obtain ⟨hdomR', hdvrR', hlocR', hidxR'⟩ :=
      NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes z ζ₀ hζ₀sp hζ₀max halgZ
    haveI := hdomR'; haveI := hdvrR'; haveI := hlocR'
    haveI : IsLocalHom (algebraMap (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
      RingHom.isLocalHom_comp (v.stalkMap ηU).hom ((pullback.fst z T.f).stalkMap η').hom
    have hO : Ideal.map (algebraMap (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)) (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ := by
      rw [← hidxR'.map_maximalIdeal, Ideal.map_map]
      exact hidxO.map_maximalIdeal

    obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr
    have hϖO : algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ηU) ϖ ≠ 0 := C7Glue.map_uniformizer_ne_zero _ ϖ hϖ hidxO.map_maximalIdeal
    have hϖR' : algebraMap R (Z.presheaf.stalk ζ₀) ϖ ≠ 0 := C7Glue.map_uniformizer_ne_zero _ ϖ hϖ hidxR'.map_maximalIdeal
    have hinjRO : Function.Injective (algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
      C7Glue.injective_of_map_irreducible_ne_zero _ ϖ hϖirr hϖO
    have hinjRR' : Function.Injective (algebraMap R (Z.presheaf.stalk ζ₀)) :=
      C7Glue.injective_of_map_irreducible_ne_zero _ ϖ hϖirr hϖR'
    have hinjR'O : Function.Injective (algebraMap (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
      C7Glue.injective_of_map_irreducible_ne_zero _ (algebraMap R (Z.presheaf.stalk ζ₀) ϖ)
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
          (C7Glue.maximalIdeal_eq_span_map _ ϖ hϖ hidxR'.map_maximalIdeal))
        (by rw [← IsScalarTower.algebraMap_apply R (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)]; exact hϖO)
    have hinjXO : Function.Injective (algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := by
      obtain ⟨hdomX, hdvrX, hlocX, hidxX⟩ :=
        NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes f ((pullback.snd z f).base (U₀.ι.base ηU)) hξsp hξmax halgX
      haveI := hdomX; haveI := hdvrX
      exact C7Glue.injective_of_map_irreducible_ne_zero _ (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ϖ)
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
          (C7Glue.maximalIdeal_eq_span_map _ ϖ hϖ hidxX.map_maximalIdeal))
        (by rw [← IsScalarTower.algebraMap_apply R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU)]; exact hϖO)
    let F := FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)
    haveI : IsScalarTower (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') F := IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) F, IsScalarTower.algebraMap_apply (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) F,
        ← IsScalarTower.algebraMap_apply (Z.presheaf.stalk ζ₀) ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU)])
    haveI : IsScalarTower R (Z.presheaf.stalk ζ₀) F := IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) F, IsScalarTower.algebraMap_apply R ((U₀ : Scheme.{u}).presheaf.stalk ηU) F,
        ← IsScalarTower.algebraMap_apply R (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU)])
    haveI : IsScalarTower R (T.Y.presheaf.stalk y₁) F := IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply (T.Y.presheaf.stalk y₁) ((U₀ : Scheme.{u}).presheaf.stalk ηU) F, IsScalarTower.algebraMap_apply R ((U₀ : Scheme.{u}).presheaf.stalk ηU) F,
        ← IsScalarTower.algebraMap_apply R (T.Y.presheaf.stalk y₁) ((U₀ : Scheme.{u}).presheaf.stalk ηU)])
    haveI : IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) F := IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) F, IsScalarTower.algebraMap_apply R ((U₀ : Scheme.{u}).presheaf.stalk ηU) F,
        ← IsScalarTower.algebraMap_apply R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU)])
    haveI : FaithfulSMul R F := (faithfulSMul_iff_algebraMap_injective R F).mpr (by
      rw [IsScalarTower.algebraMap_eq R ((U₀ : Scheme.{u}).presheaf.stalk ηU) F]; exact (IsFractionRing.injective ((U₀ : Scheme.{u}).presheaf.stalk ηU) F).comp hinjRO)
    letI algKF : Algebra K F := (IsFractionRing.lift (g := algebraMap R F) (FaithfulSMul.algebraMap_injective R F)).toAlgebra
    haveI : IsScalarTower R K F := IsScalarTower.of_algebraMap_eq (fun x =>
      (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective R F) x).symm)
    let K' := FractionRing (Z.presheaf.stalk ζ₀)
    haveI : FaithfulSMul R K' := (faithfulSMul_iff_algebraMap_injective R K').mpr (by
      rw [IsScalarTower.algebraMap_eq R (Z.presheaf.stalk ζ₀) K']; exact (IsFractionRing.injective (Z.presheaf.stalk ζ₀) K').comp hinjRR')
    letI algKK' : Algebra K K' := (IsFractionRing.lift (g := algebraMap R K') (FaithfulSMul.algebraMap_injective R K')).toAlgebra
    haveI : IsScalarTower R K K' := IsScalarTower.of_algebraMap_eq (fun x =>
      (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective R K') x).symm)
    haveI : FaithfulSMul (Z.presheaf.stalk ζ₀) F := (faithfulSMul_iff_algebraMap_injective (Z.presheaf.stalk ζ₀) F).mpr (by
      rw [IsScalarTower.algebraMap_eq (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) F]; exact (IsFractionRing.injective ((U₀ : Scheme.{u}).presheaf.stalk ηU) F).comp hinjR'O)
    letI algK'F : Algebra K' F := FractionRing.liftAlgebra (Z.presheaf.stalk ζ₀) F
    haveI : IsScalarTower (Z.presheaf.stalk ζ₀) K' F := FractionRing.isScalarTower_liftAlgebra (Z.presheaf.stalk ζ₀) F
    haveI : IsScalarTower R K' F := IsScalarTower.of_algebraMap_eq (fun r => by
      rw [IsScalarTower.algebraMap_apply R (Z.presheaf.stalk ζ₀) K' r, ← IsScalarTower.algebraMap_apply (Z.presheaf.stalk ζ₀) K' F,
        ← IsScalarTower.algebraMap_apply R (Z.presheaf.stalk ζ₀) F])
    haveI : IsScalarTower K K' F := IsScalarTower.of_algebraMap_eq (fun x => by
      have h : (algebraMap K' F).comp (algebraMap K K') = algebraMap K F :=
        IsLocalization.ringHom_ext (nonZeroDivisors R) (by
          ext r
          simp only [RingHom.comp_apply]
          rw [← IsScalarTower.algebraMap_apply R K K', ← IsScalarTower.algebraMap_apply R K' F,
            ← IsScalarTower.algebraMap_apply R K F])
      exact (RingHom.congr_fun h x).symm)

    have hbc' := AlgebraicGeometry.bijective_kaehlerDifferential_map_comp_mapBaseChange_stalk_pullback T.f z η' halgZ halg₁
    have hRO : algebraMap (Z.presheaf.stalk ζ₀) F = (algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ηU) F).comp ((v.stalkMap ηU).hom.comp ((pullback.fst z T.f).stalkMap η').hom) := by
      rw [IsScalarTower.algebraMap_eq (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) F]; rfl
    have hτF : algebraMap (T.Y.presheaf.stalk y₁) F = (algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ηU) F).comp ((v.stalkMap ηU).hom.comp ((pullback.snd z T.f).stalkMap η').hom) := by
      rw [IsScalarTower.algebraMap_eq (T.Y.presheaf.stalk y₁) ((U₀ : Scheme.{u}).presheaf.stalk ηU) F]; rfl
    have htrans := NeronModelInfra.mul_pointGenericFibre_eq_pointGenericFibre_comp_chart_of_genericFibreRestrict_comp_eq_mul K LXK d ω X f e Z z uK η T U₀ hηU τ₀ hτ₀ v hv₁ hv₂ halgZ halgO halg₁ K' F hRO hτF

    obtain ⟨U'', hU'', algU'', hKU'', hx'', ωU'', hωU''⟩ : ∃ (U'' : XK.Opens) (hU'' : IsAffineOpen U'')
        (algU'' : Algebra Γ(XK, U'') F) (_ : letI := gK.sectionsAlgebra U''; IsScalarTower K Γ(XK, U'') F)
        (_ : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U'') F)) ≫ hU''.fromSpec =
          (NeronModelInfra.schemeHomOverComp
            (pointGenericFibre (K := K) (K' := F)
              (⟨T.Y.fromSpecStalk y₁, halg₁⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁)))) T.f))
            T.e).1)
        (ωU'' : ⋀[Γ(XK, U'')]^d (gK.kaehlerPresheaf.obj (op U''))),
        gK.topToSections d U'' ωU'' = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω := by
      exact T3Glue.exists_affine_chart_of_point gK d ω F _
        (NeronModelInfra.schemeHomOverComp
          (pointGenericFibre (K := K) (K' := F)
            (⟨T.Y.fromSpecStalk y₁, halg₁⟩ :
              SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁)))) T.f))
          T.e).2
    obtain ⟨b₁, w₁, hread⟩ :=
      NeronModelInfra.ComponentReading.exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes
        ϖ hϖ K hωframe T y₁ hy₁sp hgen₁ halg₁ F U'' hU'' hKU'' hx'' ωU'' hωU''

    obtain ⟨c, φ, hc, hφbij, hφloc, hφR, algF₀F, hTowO₀, hTowK, hxX⟩ :=
      NeronModelInfra.MinimalComponentData.exists_ringHom_stalk_chart_comp_eq_pointGenericFibre_of_forall_specializes K d ω D X f e V j hyV hVK hjopen hjchart hcover ((pullback.snd z f).base (U₀.ι.base ηU)) hξsp hξmax halgX F
        (by rw [IsScalarTower.algebraMap_eq (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) F]; exact (IsFractionRing.injective ((U₀ : Scheme.{u}).presheaf.stalk ηU) F).comp hinjXO)
    letI := (D.C c).algebra
    letI := (D.C c).algebraK
    haveI := (D.C c).isScalarTower
    letI := algF₀F
    letI algO₀O : Algebra ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := ((algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).comp φ).toAlgebra
    haveI : IsScalarTower ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F := IsScalarTower.of_algebraMap_eq (fun x => by
      have h := @IsScalarTower.algebraMap_apply ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F _ _ _ _ _ (((algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) F).comp φ).toAlgebra) hTowO₀ x
      rw [← h, IsScalarTower.algebraMap_apply ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU) F x]
      show _ = (algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) F) (φ x)
      rw [IsScalarTower.algebraMap_apply (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) F (φ x)]
      rfl)
    haveI : IsScalarTower R ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU) := IsScalarTower.of_algebraMap_eq (fun r => by
      show algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ηU) r = algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU) (φ (algebraMap R ((D.C c).Y.presheaf.stalk (D.C c).y) r))
      rw [← RingHom.comp_apply φ, hφR, ← IsScalarTower.algebraMap_apply R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) ((U₀ : Scheme.{u}).presheaf.stalk ηU)])
    haveI : IsScalarTower R ((D.C c).Y.presheaf.stalk (D.C c).y) F := IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU) F, IsScalarTower.algebraMap_apply R ((U₀ : Scheme.{u}).presheaf.stalk ηU) F,
        ← IsScalarTower.algebraMap_apply R ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU)])
    haveI : IsLocalHom (algebraMap ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU)) :=
      @RingHom.isLocalHom_comp _ _ _ _ _ _ ((U₀.ι ≫ pullback.snd z f).stalkMap ηU).hom φ inferInstance hφloc
    haveI : IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F := hTowK
    obtain ⟨hdomO₀, hdvrO₀, hlocO₀, hidxO₀⟩ :=
      NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes (D.C c).f (D.C c).y (D.C c).hy
        (D.C c).hmax (D.C c).halg
    haveI := hlocO₀

    have hbc : Function.Bijective
        ((KaehlerDifferential.map R (Z.presheaf.stalk ζ₀) ((U₀ : Scheme.{u}).presheaf.stalk ηU) ((U₀ : Scheme.{u}).presheaf.stalk ηU)).restrictScalars ((U₀ : Scheme.{u}).presheaf.stalk ηU) ∘ₗ
          KaehlerDifferential.mapBaseChange R ((D.C c).Y.presheaf.stalk (D.C c).y) ((U₀ : Scheme.{u}).presheaf.stalk ηU)) := by
      exact T3Glue.bijective_map_comp_mapBaseChange_stalk_of_isOpenImmersion f z U₀.ι ηU
        (v ≫ pullback.fst z T.f) hv₁ ζ₀ rfl halgZ halgX ((D.C c).Y.presheaf.stalk (D.C c).y) φ hφbij hφR
        (fun a => by
          rw [Scheme.Hom.stalkMap_comp]
          simp [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]
          rfl)
        (fun b => rfl)

    letI := gK.sectionsAlgebra (D.C c).U
    letI := (D.C c).algebraU
    letI algUcF : Algebra Γ(XK, (D.C c).U) F := ((algebraMap (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F).comp (algebraMap Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)))).toAlgebra
    letI := gK.sectionsAlgebra U''
    letI := algU''
    haveI := hKU''
    have hKUc : IsScalarTower K Γ(XK, (D.C c).U) F := IsScalarTower.of_algebraMap_eq (fun x => by
      show algebraMap K F x = algebraMap (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F (algebraMap Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (algebraMap K Γ(XK, (D.C c).U) x))
      rw [← @IsScalarTower.algebraMap_apply K Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) _ _ _ (gK.sectionsAlgebra (D.C c).U)
        (D.C c).algebraU _ (D.C c).isScalarTowerU x, ← IsScalarTower.algebraMap_apply K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F])
    haveI := hKUc
    haveI : IsFractionRing ((pullback z T.f).presheaf.stalk η') F := by
      have e : (((algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ηU) F).comp (v.stalkMap ηU).hom).toAlgebra : Algebra ((pullback z T.f).presheaf.stalk η') F) =
          (inferInstance : Algebra ((pullback z T.f).presheaf.stalk η') F) :=
        Algebra.algebra_ext _ _ (fun r => (IsScalarTower.algebraMap_apply ((pullback z T.f).presheaf.stalk η') ((U₀ : Scheme.{u}).presheaf.stalk ηU) F r).symm)
      exact (congrArg (fun i : Algebra ((pullback z T.f).presheaf.stalk η') F => @IsLocalization _ _ (nonZeroDivisors _) F _ i) e).mp hfrac
    have hxpt : (NeronModelInfra.schemeHomOverComp
          (pointGenericFibre (K := K) (K' := F)
            (⟨(U₀ : Scheme.{u}).fromSpecStalk ηU, halgO⟩ :
              SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ηU)))) (U₀.ι ≫ pullback.fst z f ≫ z)))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U₀.ι ≫ pullback.fst z f ≫ z)
              ⟨U₀.ι ≫ pullback.snd z f, by rw [Category.assoc, ← pullback.condition]⟩) e)).1 =
        (NeronModelInfra.schemeHomOverComp
          (pointGenericFibre (K := K) (K' := F)
            (⟨X.fromSpecStalk ((pullback.snd z f).base (U₀.ι.base ηU)), halgX⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))))) f))
          e).1 := by

      have hFpt : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU))) F)) ≫
            X.fromSpecStalk ((pullback.snd z f).base (U₀.ι.base ηU)) =
          Spec.map (CommRingCat.ofHom (algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ηU) F)) ≫
            (U₀ : Scheme.{u}).fromSpecStalk ηU ≫ (U₀.ι ≫ pullback.snd z f) := by
        rw [IsScalarTower.algebraMap_eq (X.presheaf.stalk ((pullback.snd z f).base (U₀.ι.base ηU)))
          ((U₀ : Scheme.{u}).presheaf.stalk ηU) F, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
        erw [← Scheme.SpecMap_stalkMap_fromSpecStalk (U₀.ι ≫ pullback.snd z f) (x := ηU)]
        rfl
      simp only [NeronModelInfra.schemeHomOverComp_coe]
      rw [← Category.assoc, G2Glue.pointGenericFibre_comp_genericFibreRestrict K f (U₀.ι ≫ pullback.fst z f ≫ z)
        (U₀.ι ≫ pullback.snd z f) (by rw [Category.assoc, ← pullback.condition]) ηU
        ((pullback.snd z f).base (U₀.ι.base ηU)) halgO halgX F hFpt]
    have hleftη : TopFormOrder.topFormMap K K' Γ(XK, U'') F d ωU'' = TopFormOrder.topFormMap K K' Γ(XK, (D.C c).U) F d (D.C c).ωU :=
      hleft K' F _ _ (D.C c).U U'' (D.C c).hU hU'' (hxX.trans hxpt.symm) (hx''.trans htrans.symm)
        (D.C c).ωU ωU'' (D.C c).hωU hωU''

    have towUcF₀F : IsScalarTower Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hX : TopFormOrder.topFormMap K K' F F d (TopFormOrder.topFormMap K K Γ(XK, U'') F d ωU'') =
        TopFormOrder.topFormMap K K' (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F d
          ((D.C c).a • TopFormOrder.topFormMap R K ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) d (exteriorPower.ιMulti ((D.C c).Y.presheaf.stalk (D.C c).y) d (D.C c).b)) := by
      rw [@tfm_KK K K' Γ(XK, U'') F _ _ _ _ (gK.sectionsAlgebra U'') _ algU'' _ _ hKU'' _ d ωU'', hleftη, ← (D.C c).ha,
        @tfm_KE K K' Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F _ _ _ _ (gK.sectionsAlgebra (D.C c).U) _ _ (D.C c).algebraU _ _
          towUcF₀F (D.C c).algebraK (D.C c).isScalarTowerU _ _ hTowK _ hKUc d (D.C c).ωU]
    have hmin : TopFormOrder.addOrd ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) (D.C c).a ≤ T.n := hD.1 c T
    have hsq := NeronModelInfra.TopFormOrder.eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le R K (Z.presheaf.stalk ζ₀) K' ϖ hϖ hidxR'.map_maximalIdeal ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) hidxO₀.map_maximalIdeal
      d (D.C c).b (D.C c).a (D.C c).ha0 (T.Y.presheaf.stalk y₁) ((pullback z T.f).presheaf.stalk η') b₁ w₁ T.n hbc' ((U₀ : Scheme.{u}).presheaf.stalk ηU) F hO hbc
      (TopFormOrder.topFormMap K K Γ(XK, U'') F d ωU'') hread hX hmin
    exact ⟨⟨c, hsq.1⟩, hsq.2⟩
  refine ⟨hmain.1, ?_⟩

  haveI := Algebra.FormallyEtale.of_formallySmooth_of_bijective_mapBaseChange hmain.2
  exact inferInstance

end S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
end P2MW
export P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul (solution)
