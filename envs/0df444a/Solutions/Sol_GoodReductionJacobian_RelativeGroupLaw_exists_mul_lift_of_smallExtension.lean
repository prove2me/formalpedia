-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_smallExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/924a14f7-20c9-55cd-b84c-24fff4ad3023

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_orderedAffineCover_lift_mul_of_smooth
import Theorems.Thm_AlgebraicGeometry_exists_isPullback_fibre_prod_and_slices_of_section
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_appTop_fibre_of_isPullback
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_mul_lift_comp_eq_of_exists_mul_lift
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_pointDerivations_obstruction_cocycle_of_local_lifts_anyResidueField
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_mul_lift_of_pointDerivations_coboundary_anyResidueField
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_ringEquiv_tensor_sections_baseChange_inter
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_IsLocalRing_exists_module_residueField_linearMap_range_eq_ker_ringHom_of_mul_maximalIdeal_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_mul_lift_of_smallExtension
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

namespace K2BodyEd2

theorem exists_pointDerivations_comp_eq {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R] (ev : R →+* k)
    {W C0 C1 : Type u} [AddCommGroup W] [Module k W] [AddCommGroup C0] [Module k C0] [AddCommGroup C1] [Module k C1]
    (d : C0 →ₗ[k] C1) (c : ↥(Algebra.PointDerivations k R ev (W →ₗ[k] C1)))
    (h : ∀ (a : R) (w : W), ∃ b : C0, d b = c.1 a w) :
    ∃ b : ↥(Algebra.PointDerivations k R ev (W →ₗ[k] C0)), ∀ (a : R) (w : W), d (b.1 a w) = c.1 a w := by
  classical
  obtain ⟨g₀, hg₀⟩ := LinearMap.exists_rightInverse_of_surjective d.rangeRestrict (LinearMap.range_rangeRestrict d)
  have hmem : ∀ (a : R) (w : W), c.1 a w ∈ LinearMap.range d := fun a w => by
    obtain ⟨b, hb⟩ := h a w; exact ⟨b, hb⟩

  let β : R → (W →ₗ[k] C0) := fun a => g₀.comp ((c.1 a).codRestrict (LinearMap.range d) (hmem a))
  have hβ : ∀ a w, β a w = g₀ ⟨c.1 a w, hmem a w⟩ := fun a w => rfl
  have hβd : ∀ a w, d (β a w) = c.1 a w := by
    intro a w
    have := LinearMap.congr_fun hg₀ ⟨c.1 a w, hmem a w⟩
    rw [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [hβ]
    exact congrArg Subtype.val this

  have hβadd : ∀ a a', β (a + a') = β a + β a' := by
    intro a a'; ext w
    rw [LinearMap.add_apply, hβ, hβ, hβ, ← map_add]
    congr 1; apply Subtype.ext
    simp only [Submodule.coe_add, map_add, LinearMap.add_apply]
  have hβsmul : ∀ (r : k) a, β (r • a) = r • β a := by
    intro r a; ext w
    rw [LinearMap.smul_apply, hβ, hβ, ← map_smul]
    congr 1; apply Subtype.ext
    simp only [Submodule.coe_smul, map_smul, LinearMap.smul_apply]
  let βlin : R →ₗ[k] (W →ₗ[k] C0) := { toFun := β, map_add' := hβadd, map_smul' := hβsmul }
  refine ⟨⟨βlin, fun a a' => ?_⟩, fun a w => hβd a w⟩
  ext w
  show β (a * a') w = (ev a • β a' + ev a' • β a) w
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, hβ, hβ, hβ, ← map_smul, ← map_smul, ← map_add]
  congr 1; apply Subtype.ext
  simp only [Submodule.coe_add, Submodule.coe_smul, c.2 a a', LinearMap.add_apply, LinearMap.smul_apply]

theorem main
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (hc₀ : L₀.IsCommutative)
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of T'))) f)
    (he : Spec.map (CommRingCat.ofHom π) ≫ e.1 = (L₀.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ g) :
    ∃ m : pullback f f ⟶ A, m ≫ f = pullback.fst f f ≫ f ∧
      pullback.lift e.1 e.1 rfl ≫ m = e.1 ∧
      (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ≫ m =
        (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g := by
  classical
  by_cases hI : RingHom.ker π ≤ maximalIdeal T'
  swap
  ·
    obtain ⟨x, hxk, hxm⟩ := Set.not_subset.mp hI
    have hu : IsUnit x := of_not_not ((IsLocalRing.mem_maximalIdeal x).not.mp hxm)
    have hπx : π x = 0 := (RingHom.mem_ker).mp hxk
    have h01 : (0 : T) = 1 := isUnit_zero_iff.mp (hπx ▸ hu.map π)
    haveI : Subsingleton T := subsingleton_of_zero_eq_one h01
    haveI : IsEmpty ↥(Spec (CommRingCat.of T)) := show IsEmpty (PrimeSpectrum T) from inferInstance
    haveI : IsEmpty ↥(pullback f₀ f₀) := ⟨fun p => IsEmpty.false ((pullback.fst f₀ f₀ ≫ f₀).base p)⟩
    refine ⟨pullback.fst f f, rfl, pullback.lift_fst _ _ _, ?_⟩
    exact Limits.IsInitial.hom_ext (AlgebraicGeometry.isInitialOfIsEmpty) _ _

  have hle : ∀ a ∈ RingHom.ker π, residue T' a = 0 := fun a ha =>
    (Ideal.Quotient.eq_zero_iff_mem).mpr (hI ha)
  let ρ : T →+* ResidueField T' :=
    (Ideal.Quotient.lift (RingHom.ker π) (residue T') hle).comp (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hρ : ρ.comp π = residue T' := by
    ext a
    have h1 : (RingHom.quotientKerEquivOfSurjective hπ) (Ideal.Quotient.mk (RingHom.ker π) a) = π a := by
      simp [RingHom.quotientKerEquivOfSurjective]
    have h2 : (RingHom.quotientKerEquivOfSurjective hπ).symm (π a) = Ideal.Quotient.mk (RingHom.ker π) a := by
      rw [← h1, RingEquiv.symm_apply_apply]
    show (Ideal.Quotient.lift (RingHom.ker π) (residue T') hle) ((RingHom.quotientKerEquivOfSurjective hπ).symm (π a)) = residue T' a
    rw [h2, Ideal.Quotient.lift_mk]

  obtain ⟨V, _, _, _, _, _, _, _, ι, hι, hιI⟩ :
      ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module (ResidueField T') V) (_ : Module.Finite (ResidueField T') V)
        (_ : Module T' V) (_ : IsScalarTower T' (ResidueField T') V)
        (_ : Module (ResidueField T')ᵐᵒᵖ V) (_ : IsCentralScalar (ResidueField T') V) (ι : V →ₗ[T'] T'),
        Function.Injective ι ∧ LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π) :=
    IsLocalRing.exists_module_residueField_linearMap_range_eq_ker_ringHom_of_mul_maximalIdeal_eq_bot π hsmall

  haveI := hp
  haveI := hs
  haveI : IsSeparated (pullback.fst f f ≫ f) := inferInstance

  obtain ⟨𝒲, m, hmf, hmμ⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_orderedAffineCover_lift_mul_of_smooth T' T π hπ hker f₀ L₀ h₀ f hs hp g hg

  let sρ : Spec (CommRingCat.of (ResidueField T')) ⟶ Spec (CommRingCat.of T) := Spec.map (CommRingCat.ofHom ρ)
  let fk := RelativeGroupLaw.baseChangeStr sρ f₀
  let i₀ : pullback f₀ sρ ⟶ A₀ := pullback.fst f₀ sρ
  have hi₀ : IsPullback i₀ fk f₀ sρ := IsPullback.of_hasPullback f₀ sρ
  let Lk : RelativeGroupLaw (ResidueField T') fk := L₀.baseChange sρ

  obtain ⟨Ue, hUe, e₁, he₁⟩ : ∃ (Ue : (pullback f₀ sρ).Opens) (_ : IsAffineOpen Ue)
      (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})), e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1 := by
    let pt : ↥(Spec (CommRingCat.of (ResidueField T'))) := ⟨⊥, Ideal.isPrime_bot⟩
    obtain ⟨U', hU'aff, hmem, -⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.Scheme.isBasis_affineOpens (pullback f₀ sρ)))
        (show (Lk.one (𝟙 _)).1.base pt ∈ (⊤ : (pullback f₀ sρ).Opens) from trivial)
    let Ue : (pullback f₀ sρ).Opens := U'
    have hrange : Set.range (Lk.one (𝟙 _)).1.base ⊆ Set.range Ue.ι.base := by
      rintro _ ⟨y, rfl⟩
      have : y = pt := Subsingleton.elim _ _
      rw [this, Scheme.Opens.range_ι]
      exact hmem
    exact ⟨Ue, hU'aff, IsOpenImmersion.lift Ue.ι (Lk.one (𝟙 _)).1 hrange, IsOpenImmersion.lift_fac _ _ _⟩

  let sr : Spec (CommRingCat.of (ResidueField T')) ⟶ Spec (CommRingCat.of T') := Spec.map (CommRingCat.ofHom (residue T'))
  let bk := pullback.fst (pullback.fst f f ≫ f) sr
  let yk := pullback.snd (pullback.fst f f ≫ f) sr
  have hbk : IsPullback bk yk (pullback.fst f f ≫ f) sr := IsPullback.of_hasPullback _ _
  haveI : IsAffineHom sr := inferInstance
  haveI : IsAffineHom bk := MorphismProperty.pullback_fst _ _ inferInstance
  have hσ : ∀ (n : ℕ) (s : 𝒲.Idx n),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      letI := algebraOfHom yk ((𝒲.comap bk).inter s)
      ∃ σ : ((ResidueField T') ⊗[T'] Γ(pullback f f, 𝒲.inter s)) ≃+* Γ(pullback (pullback.fst f f ≫ f) sr, (𝒲.comap bk).inter s),
        (∀ x : Γ(pullback f f, 𝒲.inter s), σ ((1 : ResidueField T') ⊗ₜ[T'] x) =
          ((pullback (pullback.fst f f ≫ f) sr).presheaf.map (homOfLE (𝒲.comap_inter_le bk s)).op).hom ((bk.app (𝒲.inter s)).hom x)) ∧
        (∀ a : ResidueField T', σ (a ⊗ₜ[T'] (1 : Γ(pullback f f, 𝒲.inter s))) =
          algebraMap (ResidueField T') Γ(pullback (pullback.fst f f ≫ f) sr, (𝒲.comap bk).inter s) a) :=
    fun n s => AlgebraicGeometry.Scheme.OrderedAffineCover.exists_ringEquiv_tensor_sections_baseChange_inter
      (pullback.fst f f ≫ f) 𝒲 (ResidueField T') s
  choose σ hσ₁ hσ₂ using hσ

  have haK : IsPullback (i₀ ≫ g) fk f sr := by
    have := hi₀.paste_horiz hg
    rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ] at this

  obtain ⟨p₁, p₂, ek, iX, iY, hp₁, hp₁k, hp₂, hp₂k, hPk, hek, hekk, hiXc, hiX₁, hiX₂, hiXP, hiYc, hiY₁, hiY₂, hiYP⟩ :=
    AlgebraicGeometry.exists_isPullback_fibre_prod_and_slices_of_section (residue T') f e.1 e.2 (i₀ ≫ g) fk haK
  haveI := hiXc
  haveI := hiYc

  have hX := GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_appTop_fibre_of_isPullback h₀ ρ fk i₀ hi₀
  haveI : IsProper fk := (h₀.of_isPullback hi₀).proper
  haveI : QuasiCompact fk := inferInstance
  haveI : IsSeparated fk := inferInstance

  obtain ⟨c, hO1, hO2, hO3X, hO3Y⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_pointDerivations_obstruction_cocycle_of_local_lifts_anyResidueField
      T' T π hπ hker hsmall f₀ L₀ hc₀ h₀ f hs hp g hg e he hI ρ hρ V ι hι hιI 𝒲 m hmf hmμ fk Lk i₀ hi₀ Ue hUe e₁ he₁
      bk yk hbk (fun {n} s => σ n s) (fun {n} s => hσ₁ n s) (fun {n} s => hσ₂ n s)
      p₁ p₂ hp₁ hp₁k hp₂ hp₂k hPk ek hek hekk iX hiX₁ hiX₂ hiXP iY hiY₁ hiY₂ hiYP

  have hbdry : ∀ (a : Γ(pullback f₀ sρ, Ue)) (ξ : Module.Dual (ResidueField T') V),
      ∃ b : (OModulePresheaf.unit (p₁ ≫ fk)).cochain (𝒲.comap bk) 0,
        (OModulePresheaf.unit (p₁ ≫ fk)).d (𝒲.comap bk) 0 b = c.1 a ξ :=
    fun a ξ => AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap
      fk fk hX hX ek hekk ek hekk p₁ p₂ hPk iX hiX₁ hiX₂ iY hiY₁ hiY₂ (𝒲.comap bk) (c.1 a ξ) (hO2 a ξ) (hO3X a ξ) (hO3Y a ξ)

  obtain ⟨b, hb⟩ : letI := algebraOfHom fk Ue
      ∃ b : ↥(Algebra.PointDerivations (ResidueField T') Γ(pullback f₀ sρ, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit (p₁ ≫ fk)).cochain (𝒲.comap bk) 0)),
        ∀ (a : Γ(pullback f₀ sρ, Ue)) (ξ : Module.Dual (ResidueField T') V),
          (OModulePresheaf.unit (p₁ ≫ fk)).d (𝒲.comap bk) 0 (b.1 a ξ) = c.1 a ξ := by
    letI := algebraOfHom fk Ue
    exact exists_pointDerivations_comp_eq _ ((OModulePresheaf.unit (p₁ ≫ fk)).d (𝒲.comap bk) 0) c hbdry

  obtain ⟨m', hm'f, hm'μ⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_pointDerivations_coboundary_anyResidueField
      T' T π hπ hker hsmall f₀ L₀ hc₀ h₀ f hs hp g hg e he hI ρ hρ V ι hι hιI 𝒲 m hmf hmμ fk Lk i₀ hi₀ Ue hUe e₁ he₁
      bk yk hbk (fun {n} s => σ n s) (fun {n} s => hσ₁ n s) (fun {n} s => hσ₂ n s)
      p₁ p₂ hp₁ hp₁k hp₂ hp₂k hPk c hO1 b hb

  exact GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_comp_eq_of_exists_mul_lift
    T' T π hπ hker f₀ L₀ f hs g hg e he m' hm'f hm'μ

end K2BodyEd2

theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (hc₀ : L₀.IsCommutative)
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of T'))) f)
    (he : Spec.map (CommRingCat.ofHom π) ≫ e.1 = (L₀.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ g) :
    ∃ m : pullback f f ⟶ A, m ≫ f = pullback.fst f f ≫ f ∧
      pullback.lift e.1 e.1 rfl ≫ m = e.1 ∧
      pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
          (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition]) ≫ m =
        (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g := by
  exact K2BodyEd2.main T' T π hπ hker hsmall f₀ L₀ hc₀ h₀ f hs hp g hg e he

end S_GoodReductionJacobian_RelativeGroupLaw_exists_mul_lift_of_smallExtension
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_mul_lift_of_smallExtension (solution)
